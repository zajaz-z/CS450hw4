"""
resolve.py: a recursive resolver built using dnspython
"""


import argparse
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple

import dns.exception
import dns.flags
import dns.message
import dns.name
import dns.query
import dns.rdata
import dns.rdataclass
import dns.rdatatype
import dns.rcode


FORMATS = (("CNAME", "{alias} is an alias for {name}"),
           ("A", "{name} has address {address}"),
           ("AAAA", "{name} has IPv6 address {address}"),
           ("MX", "{name} mail is handled by {preference} {exchange}"))

ROOT_SERVERS = ("198.41.0.4", "199.9.14.201", "192.33.4.12",
                "199.7.91.13", "192.203.230.10", "192.5.5.241",
                "192.112.36.4", "198.97.190.53", "192.36.148.17",
                "192.58.128.30", "193.0.14.129", "199.7.83.42",
                "202.12.27.33")

TIMEOUT = 3
MAX_CNAME_RESTARTS = 20

# These caches intentionally live for one invocation of the program.  Answer
# caching prevents exact duplicate lookups, while delegation caching means a
# later name under a previously visited zone can skip the root/TLD work.
ANSWER_CACHE: Dict[Tuple[str, int], dns.message.Message] = {}
DELEGATION_CACHE: Dict[str, Tuple[str, ...]] = {".": ROOT_SERVERS}


def _empty_response(query: Optional[dns.message.Message] = None) -> dns.message.Message:
    """Return a safe, empty response even if construction of a query failed."""
    try:
        return dns.message.make_response(query) if query is not None else dns.message.Message()
    except Exception:
        return dns.message.Message()


def _key(name: dns.name.Name, qtype: int) -> Tuple[str, int]:
    return (name.canonicalize().to_text().lower(), int(qtype))


def _query(server: str, name: dns.name.Name, qtype: int) -> Optional[dns.message.Message]:
    """Send exactly one non-recursive IPv4 query, treating every error as a miss."""
    try:
        # Root and TLD delegations (notably .com and .edu) often contain
        # enough NS and glue records to exceed the old 512-byte UDP limit.
        # EDNS avoids a truncated referral and the many needless recursive
        # NS-host lookups that a partial Additional section would cause.
        query = dns.message.make_query(name, qtype, use_edns=0, payload=1232)
        query.flags &= ~dns.flags.RD
        return dns.query.udp(query, server, timeout=TIMEOUT)
    except Exception:
        # Timeout, bad packets, and unreachable servers are ordinary DNS
        # conditions for this assignment, not reasons to expose a traceback.
        return None


def _best_cached_servers(name: dns.name.Name) -> Tuple[str, ...]:
    """Find the closest cached delegation which encloses *name*."""
    labels = list(name.canonicalize().labels)
    for index in range(len(labels)):
        zone = dns.name.Name(labels[index:]).to_text().lower()
        servers = DELEGATION_CACHE.get(zone)
        if servers:
            return servers
    return ROOT_SERVERS


def _rrsets(response: dns.message.Message, section: Iterable) -> Iterable:
    """Yield rrsets defensively; malformed replies must not escape lookup()."""
    try:
        yield from section
    except Exception:
        return


def _answer_has_type(response: dns.message.Message, name: dns.name.Name,
                     qtype: int) -> bool:
    for rrset in _rrsets(response, response.answer):
        if rrset.name == name and rrset.rdtype == qtype:
            return True
    return False


def _cname_target(response: dns.message.Message,
                  name: dns.name.Name) -> Optional[dns.name.Name]:
    for rrset in _rrsets(response, response.answer):
        if rrset.name == name and rrset.rdtype == dns.rdatatype.CNAME:
            try:
                return next(iter(rrset)).target
            except (StopIteration, AttributeError):
                return None
    return None


def _referral(response: dns.message.Message) -> Optional[Tuple[dns.name.Name, List[dns.name.Name], Dict[dns.name.Name, List[str]]]]:
    """Return (delegated zone, NS names, IPv4 glue indexed by NS name)."""
    nameservers: List[dns.name.Name] = []
    zone = None
    for rrset in _rrsets(response, response.authority):
        if rrset.rdtype == dns.rdatatype.NS:
            zone = rrset.name
            nameservers.extend(r.target for r in rrset)
    if zone is None or not nameservers:
        return None

    wanted = {server.canonicalize() for server in nameservers}
    glue: Dict[dns.name.Name, List[str]] = {}
    for rrset in _rrsets(response, response.additional):
        if rrset.rdtype == dns.rdatatype.A and rrset.name.canonicalize() in wanted:
            glue[rrset.name.canonicalize()] = [str(record) for record in rrset]
    return zone, nameservers, glue


def _append_answers(destination: dns.message.Message,
                    source: dns.message.Message) -> None:
    """Append answer rrsets without duplicating a set already collected."""
    present = {(rr.name, rr.rdtype, rr.rdclass, rr.to_text())
               for rr in destination.answer}
    for rrset in _rrsets(source, source.answer):
        identity = (rrset.name, rrset.rdtype, rrset.rdclass, rrset.to_text())
        if identity not in present:
            destination.answer.append(rrset)
            present.add(identity)


def _resolve_nameserver_addresses(nameservers: Sequence[dns.name.Name],
                                  resolving: Set[str]) -> List[str]:
    """Find IPv4 addresses for unglued NS records using the same resolver."""
    addresses: List[str] = []
    for nameserver in nameservers:
        ns_key = nameserver.canonicalize().to_text().lower()
        # A cyclic out-of-bailiwick delegation cannot be made useful by
        # recursing forever.  Other nameservers in the referral may still work.
        if ns_key in resolving:
            continue
        cache_key = _key(nameserver, dns.rdatatype.A)
        response = ANSWER_CACHE.get(cache_key)
        if response is None:
            response = _iterative_lookup(nameserver, dns.rdatatype.A,
                                         resolving | {ns_key})
            ANSWER_CACHE[cache_key] = response
        for rrset in _rrsets(response, response.answer):
            if rrset.rdtype == dns.rdatatype.A:
                addresses.extend(str(record) for record in rrset)
    return addresses


def _iterative_lookup(target_name: dns.name.Name, qtype: int,
                      resolving: Optional[Set[str]] = None) -> dns.message.Message:
    """Iteratively resolve one DNS name and follow CNAMEs for non-CNAME asks."""
    query = None
    try:
        query = dns.message.make_query(target_name, qtype)
    except Exception:
        return _empty_response()

    resolving = set() if resolving is None else set(resolving)
    result = _empty_response(query)
    current_name = target_name
    cname_hops = 0

    while cname_hops <= MAX_CNAME_RESTARTS:
        servers = list(_best_cached_servers(current_name))
        visited_servers: Set[str] = set()
        pending_nameservers: List[dns.name.Name] = []
        delegation_zone: Optional[str] = None
        cname_restart = False

        # At each delegation, try every supplied IPv4 address.  For an
        # unglued referral, resolve NS hostnames lazily: there is no reason to
        # resolve (and wait for) every NS hostname when the first one can
        # immediately answer the original question.
        while servers or pending_nameservers:
            if not servers:
                nameserver = pending_nameservers.pop(0)
                discovered = _resolve_nameserver_addresses([nameserver], resolving)
                for address in discovered:
                    if address not in visited_servers and address not in servers:
                        servers.append(address)
                if delegation_zone is not None and discovered:
                    old = DELEGATION_CACHE.get(delegation_zone, ())
                    DELEGATION_CACHE[delegation_zone] = tuple(dict.fromkeys(
                        list(old) + discovered))
                continue

            server = servers.pop(0)
            if server in visited_servers:
                continue
            visited_servers.add(server)
            response = _query(server, current_name, qtype)
            if response is None:
                continue

            if response.rcode() == dns.rcode.NXDOMAIN:
                return result if result.answer else response
            if response.rcode() != dns.rcode.NOERROR:
                continue

            _append_answers(result, response)
            cname = _cname_target(response, current_name)
            if cname is not None:
                # A recursive resolver returns the *entire* alias chain even
                # when the requested type is CNAME.  Keep restarting until an
                # authoritative server returns NODATA (or the requested
                # non-CNAME record) so collect_results can print each link.
                current_name = cname
                cname_hops += 1
                cname_restart = True
                break

            if _answer_has_type(response, current_name, qtype):
                return result

            delegation = _referral(response)
            if delegation is None:
                # An authoritative NODATA response is a final answer.
                return result

            zone, ns_names, glue = delegation
            next_servers = list(dict.fromkeys(
                address for addresses in glue.values() for address in addresses))
            # Do not resolve every NS host just because a referral happened to
            # addresses than NS names.  Only hosts without A glue are queued
            # for a recursive sub-lookup, and only if the glued addresses do
            # not produce an answer.
            pending_nameservers = [ns for ns in ns_names
                                   if ns.canonicalize() not in glue]
            delegation_zone = zone.canonicalize().to_text().lower()
            # Cache any glue immediately.  Discovered unglued addresses are
            # appended as they are needed above.
            if next_servers:
                DELEGATION_CACHE[delegation_zone] = tuple(next_servers)
            servers = next_servers

        # Referrals continue in the inner loop.  Re-enter this loop only when
        # an answer CNAME changed the name being sought.
        if not cname_restart:
            return result

    return result


def lookup(target_name: dns.name.Name,
           qtype: dns.rdata.Rdata) -> dns.message.Message:
    """Resolve *target_name* without using a recursive DNS resolver."""
    try:
        key = _key(target_name, qtype)
        cached = ANSWER_CACHE.get(key)
        if cached is not None:
            return cached
        answer = _iterative_lookup(target_name, int(qtype))
        ANSWER_CACHE[key] = answer
        return answer
    except Exception:
        # lookup() is part of the command-line boundary: it always returns a
        # message so callers can print an empty (rather than crashing) result.
        return _empty_response()


def collect_results(name: str) -> dict:
    """Parse lookup responses into the data structure consumed by print_results."""
    full_response = {"CNAME": [], "A": [], "AAAA": [], "MX": []}
    try:
        target_name = dns.name.from_text(name)
        response = lookup(target_name, dns.rdatatype.CNAME)
        alias = name
        for answers in response.answer:
            for answer in answers:
                if answers.rdtype == dns.rdatatype.CNAME:
                    full_response["CNAME"].append({"name": answer, "alias": alias})
                    # Preserve dnspython's normal DNS-name formatting, as the
                    # starter implementation did, for aliases after the first.
                    alias = answer

        for rtype, label in ((dns.rdatatype.A, "A"),
                             (dns.rdatatype.AAAA, "AAAA"),
                             (dns.rdatatype.MX, "MX")):
            response = lookup(target_name, rtype)
            for answers in response.answer:
                for answer in answers:
                    if answers.rdtype != rtype:
                        continue
                    if rtype == dns.rdatatype.MX:
                        full_response[label].append({"name": answers.name,
                                                     "preference": answer.preference,
                                                     "exchange": str(answer.exchange)})
                    else:
                        full_response[label].append({"name": answers.name,
                                                     "address": str(answer)})
    except Exception:
        pass
    return full_response


def print_results(results: dict) -> None:
    """Print a lookup result in the style of the host program."""
    printed = False
    for rtype, fmt_str in FORMATS:
        for result in results.get(rtype, []):
            print(fmt_str.format(**result))
            printed = True
    if not printed:
        print("No DNS records found")


def main() -> None:
    argument_parser = argparse.ArgumentParser()
    argument_parser.add_argument("name", nargs="+", help="DNS name(s) to look up")
    argument_parser.add_argument("-v", "--verbose", help="increase output verbosity",
                                 action="store_true")
    program_args = argument_parser.parse_args()
    for a_domain_name in program_args.name:
        try:
            print_results(collect_results(a_domain_name))
        except Exception:
            # A bad name or an unexpected library failure must not terminate a
            # multi-name invocation with a traceback.
            print("Unable to resolve {}".format(a_domain_name))


if __name__ == "__main__":
    main()
