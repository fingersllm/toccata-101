"""The launch proof of a P2R-vault campaign: anyone can check, from the launch transaction alone, that the campaign a
page names is ONE vault, launched with the settings the page prints, running the published contracts.

    python launch-proof.py CONSTANTS.json LAUNCH_TXID
    python launch-proof.py CONSTANTS.json LAUNCH_TXID --tx-file TX.json      a transaction saved from the API instead

CONSTANTS.json is the block the page prints: {"network", "name", "covenantId", "settings": {"goalSompi", "minSompi",
"payee", "cancelAddress", "refundDateMs"}}. The transaction comes from that network's public API (api.kaspa.org,
api-tn10.kaspa.org; --api for another), which is trusted for the transaction's bytes: anyone who does not trust it
can save the same transaction from their own node or indexer and pass it with --tx-file. Python 3.8 or later and
nothing else; the contracts' compiled bytes are read from contracts/p2r-vault beside this tool (--contracts DIR).

What it checks, each from the chain's own bytes:
  1. the launch is accepted, and no input of it carries the campaign's id: the id is born here;
  2. exactly ONE output carries the id. Consensus accepts a launch that binds one id to two outputs, and two vaults
     would both count and both collect, up to twice the goal to the payee (the verification's F3, 2026-10-04);
  3. the id recomputes from that output and the outpoint its authorizing input spent, by the node's own formula
     (rusty-kaspa v2.1.0, consensus/core/src/hashing/covenant_id.rs: BLAKE2b-256 keyed "CovenantID");
  4. that output pays to the P2SH of the compiled campaign script with the page's settings, OPEN, total 0, count 0,
     and the compiled bytes outside the state are the pinned ones (hashes.json): the vault runs those rules and its
     code names the pledge template, so the pledges it counts run theirs;
  5. the launch data is what the launch tool accepts (p2r's check_launch_data): goal and minimum in whole KAS, the
     minimum at least 1 KAS, the goal at least the minimum, a payee the contracts can pay, a valid Schnorr cancel key,
     a date in unix milliseconds inside 2024..2031 and after the launch, an anchor no smaller than the worst case.

Exit 0: proven. Exit 1: a check failed; the campaign is not what the page says. Exit 2: nothing could be checked
(the arguments, the files, the API).
"""
import argparse
import datetime
import hashlib
import json
import os
import re
import struct
import sys
import urllib.error
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
CONTRACTS = os.path.join(HERE, "..", "..", "contracts", "p2r-vault")
NETWORKS = {"mainnet": ("kaspa", "https://api.kaspa.org"), "testnet-10": ("kaspatest", "https://api-tn10.kaspa.org")}
UA = "Mozilla/5.0 (p2r-vault launch proof)"            # the public APIs answer Python's own User-Agent with HTTP 403
KAS = 100_000_000
OPEN = 0
FEE_CAP, RESIDUE, MAX_COLLECT = KAS // 10, KAS, 16      # campaign.sil's constants
TIME_THRESHOLD = 500_000_000_000                        # below this, a lock time is a DAA score, not a time
DATE_WINDOW_MS = (1_704_067_200_000, 1_924_992_000_000)  # p2r's sane window: 2024-01-01 to 2031-01-01
SECP_P = 2 ** 256 - 2 ** 32 - 977
CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"


class Fail(Exception):
    """The campaign is not what the page says."""


class Cannot(Exception):
    """Nothing could be checked."""


def kas(sompi):
    return "%d.%08d KAS" % divmod(sompi, KAS)


def utc(ms):
    return datetime.datetime.fromtimestamp(ms / 1000, datetime.timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")


# ---- addresses, keys, the vault's script -----------------------------------------------------------------------------

def polymod(values):
    gen = (0x98F2BC8E61, 0x79B76D99E2, 0xF33E5FB3C4, 0xAE2EABE2A8, 0x1E4F43E470)
    c = 1
    for v in values:
        top = c >> 35
        c = ((c & 0x07FFFFFFFF) << 5) ^ v
        for i in range(5):
            if (top >> i) & 1:
                c ^= gen[i]
    return c ^ 1


def decode_address(address, prefix):
    """The version and payload of a Kaspa address on the network whose prefix is given; Fail for anything else."""
    head, sep, body = address.partition(":")
    if sep != ":" or head != prefix or len(body) < 9 or any(ch not in CHARSET for ch in body):
        raise Fail("%r is not a %s: address" % (address, prefix))
    data = [CHARSET.index(ch) for ch in body]
    if polymod([ord(ch) & 31 for ch in head] + [0] + data) != 0:
        raise Fail("%r: its checksum is wrong" % address)
    acc = bits = 0
    out = []
    for v in data[:-8]:
        acc, bits = (acc << 5) | v, bits + 5
        if bits >= 8:
            bits -= 8
            out.append((acc >> bits) & 255)
    if bits >= 5 or acc & ((1 << bits) - 1) or not out:
        raise Fail("%r: its padding is wrong" % address)
    return out[0], bytes(out[1:])


def kind_and_key(address, prefix):
    """The payee as the contracts carry it: kind 0 (Schnorr), 1 (ECDSA) or 8 (P2SH), and a 33-byte key (a 32-byte
    payload is followed by one zero byte)."""
    version, payload = decode_address(address, prefix)
    if {0: 32, 1: 33, 8: 32}.get(version) != len(payload):
        raise Fail("the payee %s is not a Schnorr, ECDSA or P2SH address the contracts can pay" % address)
    return version, payload + b"\x00" * (33 - len(payload))


def cancel_key(address, prefix):
    version, payload = decode_address(address, prefix)
    if version != 0 or len(payload) != 32:
        raise Fail("the cancel address %s is not a Schnorr (version 0) address" % address)
    x = int.from_bytes(payload, "big")
    if x >= SECP_P or pow((x ** 3 + 7) % SECP_P, (SECP_P - 1) // 2, SECP_P) != 1:
        raise Fail("the cancel address %s does not carry a valid x-only key: no point on secp256k1 has that x" % address)
    return payload


def push(data):
    return bytes([len(data)]) + data


def int8(v):
    """An int as the compiler stores it in state: 8 bytes, little-endian."""
    if not 0 <= v < 2 ** 63:
        raise Fail("%d does not fit the contracts' numbers" % v)
    return v.to_bytes(8, "little")


def vault_state(goal, minimum, kind, key, cancel, date):
    """The vault's state as the launch writes it: the settings, then OPEN, total 0, count 0."""
    return (push(int8(goal)) + push(int8(minimum)) + push(bytes([kind])) + push(key) + push(cancel) + push(int8(date))
            + push(int8(OPEN)) + push(int8(0)) + push(int8(0)))


def p2sh(script):
    return "aa20" + hashlib.blake2b(script, digest_size=32).hexdigest() + "87"


def covenant_id(txid, index, outputs):
    """rusty-kaspa's covenant_id(): the genesis outpoint, then each bound output's index, value, script version (0)
    and script, BLAKE2b-256 keyed "CovenantID"."""
    h = hashlib.blake2b(digest_size=32, key=b"CovenantID")
    h.update(bytes.fromhex(txid) + struct.pack("<IQ", index, len(outputs)))
    for i, value, script in outputs:
        h.update(struct.pack("<IQHQ", i, value, 0, len(script)) + script)
    return h.hexdigest()


# ---- BLAKE3, for the template hashes (not in Python's standard library) ---------------------------------------------

IV = (0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19)
PERMUTATION = (2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8)
CHUNK_START, CHUNK_END, PARENT, ROOT = 1, 2, 4, 8
M32 = 0xFFFFFFFF


def _g(s, a, b, c, d, x, y):
    s[a] = (s[a] + s[b] + x) & M32
    s[d] = ((s[d] ^ s[a]) >> 16 | (s[d] ^ s[a]) << 16) & M32
    s[c] = (s[c] + s[d]) & M32
    s[b] = ((s[b] ^ s[c]) >> 12 | (s[b] ^ s[c]) << 20) & M32
    s[a] = (s[a] + s[b] + y) & M32
    s[d] = ((s[d] ^ s[a]) >> 8 | (s[d] ^ s[a]) << 24) & M32
    s[c] = (s[c] + s[d]) & M32
    s[b] = ((s[b] ^ s[c]) >> 7 | (s[b] ^ s[c]) << 25) & M32


def _compress(cv, m, counter, block_len, flags):
    s = list(cv) + list(IV[:4]) + [counter & M32, counter >> 32 & M32, block_len, flags]
    m = list(m)
    for r in range(7):
        _g(s, 0, 4, 8, 12, m[0], m[1])
        _g(s, 1, 5, 9, 13, m[2], m[3])
        _g(s, 2, 6, 10, 14, m[4], m[5])
        _g(s, 3, 7, 11, 15, m[6], m[7])
        _g(s, 0, 5, 10, 15, m[8], m[9])
        _g(s, 1, 6, 11, 12, m[10], m[11])
        _g(s, 2, 7, 8, 13, m[12], m[13])
        _g(s, 3, 4, 9, 14, m[14], m[15])
        m = [m[i] for i in PERMUTATION]
    return [s[i] ^ s[i + 8] for i in range(8)]


def _words(block):
    return struct.unpack("<16I", block.ljust(64, b"\x00"))


def blake3(data):
    """BLAKE3's hash mode, 32 bytes out, after the reference implementation: 1024-byte chunks of 64-byte blocks, the
    chunks' chaining values merged in a left-balanced tree, the root compressed with ROOT."""
    chunks = [data[i:i + 1024] for i in range(0, len(data), 1024)] or [b""]
    stack = []
    for n, chunk in enumerate(chunks):
        cv = IV
        blocks = [chunk[i:i + 64] for i in range(0, len(chunk), 64)] or [b""]
        for j, block in enumerate(blocks[:-1]):
            cv = _compress(cv, _words(block), n, 64, CHUNK_START if j == 0 else 0)
        last = (cv, _words(blocks[-1]), n, len(blocks[-1]), (CHUNK_START if len(blocks) == 1 else 0) | CHUNK_END)
        if n == len(chunks) - 1:
            break
        cv, total = _compress(*last), n + 1
        while total & 1 == 0:
            cv, total = _compress(IV, stack.pop() + cv, 0, 64, PARENT), total >> 1
        stack.append(cv)
    while stack:
        last = (IV, tuple(stack.pop() + _compress(*last)), 0, 64, PARENT)
    cv, m, _, block_len, flags = last
    return struct.pack("<8I", *_compress(cv, m, 0, block_len, flags | ROOT))


def template_hash(prefix, suffix):
    """silverc v1.0.0's template hash (silverscript-lang/src/template.rs): BLAKE3 over the prefix and the suffix,
    each after its length as 8 little-endian bytes."""
    return blake3(struct.pack("<Q", len(prefix)) + prefix + struct.pack("<Q", len(suffix)) + suffix).hex()


# ---- the inputs ------------------------------------------------------------------------------------------------------

class Template:
    """The compiled contracts, checked against the pins before anything is built from them: each one's bytes outside
    its state by SHA-256, and its template hash recomputed from those bytes; and the campaign's code must carry the
    pledge template's hash, the one the pledges it counts must have."""

    def __init__(self, contracts):
        parts = {}
        try:
            with open(os.path.join(contracts, "hashes.json"), encoding="utf-8") as f:
                self.pins = json.load(f)
            for name, contract in (("campaign", "CrowdfundCampaign"), ("pledge", "CrowdfundPledge")):
                with open(os.path.join(contracts, "artifacts", name + ".json"), encoding="utf-8") as f:
                    compiled = json.load(f)["contracts"][contract]["compiled"]
                code = bytes(compiled["bytecode"])
                off, n = compiled["state_span"]["offset"], compiled["state_span"]["len"]
                parts[name] = (contract, code[:off], n, code[off + n:], bytes(compiled["template_hash"]).hex())
        except (OSError, ValueError, KeyError, TypeError) as e:
            raise Cannot("the compiled contracts in %s cannot be read: %s" % (contracts, e))
        self.hashes = {}
        for name, (contract, prefix, n, suffix, claimed) in parts.items():
            pin, h = self.pins.get(contract, {}), template_hash(prefix, suffix)
            if (hashlib.sha256(prefix).hexdigest() != pin.get("prefix_sha256")
                    or hashlib.sha256(suffix).hexdigest() != pin.get("suffix_sha256")
                    or h != pin.get("template_hash") or h != claimed):
                raise Cannot("artifacts/%s.json is not the pinned template (hashes.json); refusing to build from it" % name)
            self.hashes[name] = h
        _, self.prefix, self.state_len, self.suffix, _ = parts["campaign"]
        if b"\x20" + bytes.fromhex(self.hashes["pledge"]) not in self.suffix:
            raise Cannot("the campaign's code does not carry the pledge template's hash %s" % self.hashes["pledge"])
        self.sources = {}
        for name, contract in (("campaign.sil", "CrowdfundCampaign"), ("pledge.sil", "CrowdfundPledge")):
            try:
                with open(os.path.join(contracts, name), "rb") as f:
                    h = hashlib.sha256(f.read()).hexdigest()
                self.sources[name] = "%s (%s)" % (h, "the pinned source" if h == self.pins[contract]["source_sha256"]
                                                  else "NOT the pinned source")
            except OSError:
                self.sources[name] = "not beside the artifacts"

    def script(self, state):
        if len(state) != self.state_len:
            raise Fail("the vault's state is %d bytes, not %d" % (len(state), self.state_len))
        return self.prefix + state + self.suffix


def load_block(path):
    try:
        with open(path, encoding="utf-8") as f:
            b = json.load(f)
        s = b["settings"]
        block = {"network": b["network"], "name": b["name"], "covenantId": b["covenantId"],
                 "settings": {k: s[k] for k in ("goalSompi", "minSompi", "payee", "cancelAddress", "refundDateMs")}}
    except (OSError, ValueError, KeyError, TypeError) as e:
        raise Cannot("%s is not a constants block in the page's shape: %s" % (path, e))
    if block["network"] not in NETWORKS:
        raise Cannot("the network %r is not one this check knows (%s)" % (block["network"], ", ".join(NETWORKS)))
    if not re.fullmatch(r"[0-9a-f]{64}", str(block["covenantId"])):
        raise Cannot("the covenant id %r is not 64 lowercase hex digits" % block["covenantId"])
    for k in ("goalSompi", "minSompi", "refundDateMs"):
        if type(block["settings"][k]) is not int:
            raise Cannot("settings.%s is not a whole number" % k)
    return block


def fetch(api, txid):
    url = "%s/transactions/%s?inputs=true&outputs=true&resolve_previous_outpoints=light" % (api.rstrip("/"), txid)
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            return json.load(r)
    except urllib.error.HTTPError as e:
        if e.code == 404:
            raise Fail("%s does not know the transaction %s" % (api, txid))
        raise Cannot("%s answered HTTP %d" % (api, e.code))
    except (urllib.error.URLError, OSError, ValueError) as e:
        raise Cannot("%s cannot be asked: %s" % (api, e))


# ---- the proof -------------------------------------------------------------------------------------------------------

def prove(block, txid, tx, tpl, say):
    """Every check in order; Fail on the first that does not hold. Returns what the proof prints at the end."""
    prefix = NETWORKS[block["network"]][0]
    c, s = block["covenantId"], block["settings"]

    if tx.get("transaction_id") != txid:
        raise Fail("the transaction given is %s, not %s" % (tx.get("transaction_id"), txid))
    if tx.get("is_accepted") is not True:
        raise Fail("the launch %s is not accepted on %s" % (txid, block["network"]))
    when = tx.get("accepting_block_time") or tx.get("block_time")
    if not isinstance(when, int):
        raise Cannot("the transaction carries no block time")
    say("ok", "the launch is accepted (%s, accepting blue score %s)" % (utc(when), tx.get("accepting_block_blue_score")))

    inputs, outputs = tx.get("inputs") or [], tx.get("outputs") or []
    for i, inp in enumerate(inputs):
        if inp.get("covenant_id") == c:
            raise Fail("input %d already carries the id %s: the id was born before this transaction" % (i, c))
    say("ok", "no input carries the id: it is born in this transaction")

    bound = [o for o in outputs if o.get("covenant_id") == c]
    if not bound:
        raise Fail("no output of %s carries the id %s" % (txid, c))
    if len(bound) != 1:
        raise Fail("%d outputs carry the id (%s): a campaign is ONE vault; two vaults would both count and both "
                   "collect" % (len(bound), ", ".join(str(o.get("index")) for o in bound)))
    say("ok", "exactly one output carries the id: output %s" % bound[0].get("index"))
    others = [o for o in outputs if o.get("covenant_id") and o.get("covenant_id") != c]
    if others:
        say("note", "other outputs carry other ids (%s): not this campaign's" % ", ".join(str(o.get("index")) for o in others))

    try:
        auths = {int(o["covenant_authorizing_input"]) for o in bound}
        auth = auths.pop()
        inp = inputs[auth]
        genesis = (inp["previous_outpoint_hash"], int(inp["previous_outpoint_index"]))
        group = [(int(o["index"]), int(o["amount"]), bytes.fromhex(o["script_public_key"])) for o in bound]
    except (KeyError, IndexError, TypeError, ValueError) as e:
        raise Cannot("the transaction does not say what this check needs: %r" % e)
    if covenant_id(genesis[0], genesis[1], group) != c:
        raise Fail("the id does not recompute from the genesis outpoint %s:%d and the bound output" % genesis)
    say("ok", "the id recomputes from the genesis outpoint %s:%d and that output" % genesis)

    goal, minimum, date = s["goalSompi"], s["minSompi"], s["refundDateMs"]
    kind, key = kind_and_key(s["payee"], prefix)
    cancel = cancel_key(s["cancelAddress"], prefix)
    vault = bound[0]
    want = p2sh(tpl.script(vault_state(goal, minimum, kind, key, cancel, date)))
    if vault["script_public_key"] != want:
        raise Fail("output %s pays %s, not the campaign script with the page's settings, OPEN, total 0, count 0 (%s)"
                   % (vault["index"], vault["script_public_key"], want))
    say("ok", "output %s pays the compiled campaign script with the page's settings, OPEN, total 0, count 0"
        % vault["index"])

    wrong = []
    if goal % KAS or minimum % KAS:
        wrong.append("the goal and the minimum must be whole KAS")
    if minimum < KAS:
        wrong.append("the minimum must be at least 1 KAS")
    if goal < minimum:
        wrong.append("the goal must be at least the minimum")
    if date < TIME_THRESHOLD:
        wrong.append("the refund date %d is not in unix milliseconds: the contracts would read it as a DAA score, and the "
                     "date's exits would never open" % date)
    elif not DATE_WINDOW_MS[0] <= date <= DATE_WINDOW_MS[1]:
        wrong.append("the refund date %d is outside 2024-01-01..2031-01-01" % date)
    elif date <= when:
        wrong.append("the refund date %s had already passed at the launch (%s)" % (utc(date), utc(when)))
    n = -(-(goal // KAS) // max(minimum // KAS, 1))
    worst = (n + -(-n // MAX_COLLECT) + 2) * FEE_CAP + RESIDUE
    anchor = int(vault["amount"])
    if anchor < worst:
        wrong.append("the anchor %s is smaller than the worst case %s" % (kas(anchor), kas(worst)))
    if wrong:
        raise Fail("the launch data is not what the launch tool accepts: " + "; ".join(wrong))
    say("ok", "the launch data is valid; the anchor %s covers the worst case %s" % (kas(anchor), kas(worst)))

    return [
        "the campaign  %s on %s, id %s" % (block["name"], block["network"], c),
        "the settings  goal %s, minimum %s, payee %s, cancel key %s, refund date %s (%d ms)"
        % (kas(goal), kas(minimum), s["payee"], s["cancelAddress"], utc(date), date),
        "the vault     %s:%s, holding %s" % (txid, vault["index"], kas(anchor)),
        "the genesis   %s:%d" % genesis,
        "templates     campaign %s, pledge %s (recomputed from the compiled bytes; as pinned; the campaign's code "
        "carries the pledge's)" % (tpl.hashes["campaign"], tpl.hashes["pledge"]),
        "compiler      %s" % tpl.pins.get("compiler", "?"),
        "sources       campaign.sil %s; pledge.sil %s" % (tpl.sources["campaign.sil"], tpl.sources["pledge.sil"]),
    ]


def main(argv=None):
    ap = argparse.ArgumentParser(description="The launch proof of a P2R-vault campaign, checked from the chain.")
    ap.add_argument("constants", help="the page's constants block, a JSON file")
    ap.add_argument("txid", help="the launch transaction")
    ap.add_argument("--tx-file", help="the launch transaction as the API returns it, saved; no API is asked")
    ap.add_argument("--api", help="another API than the network's public one")
    ap.add_argument("--contracts", default=CONTRACTS, help="the folder holding artifacts/campaign.json and hashes.json")
    a = ap.parse_args(argv)

    def say(mark, text):
        print("  %-4s %s" % (mark, text), flush=True)

    try:
        if not re.fullmatch(r"[0-9a-f]{64}", a.txid):
            raise Cannot("the launch txid %r is not 64 lowercase hex digits" % a.txid)
        block = load_block(a.constants)
        print("The launch proof of %r on %s, launch %s" % (block["name"], block["network"], a.txid), flush=True)
        tpl = Template(a.contracts)
        if a.tx_file:
            try:
                with open(a.tx_file, encoding="utf-8") as f:
                    tx = json.load(f)
            except (OSError, ValueError) as e:
                raise Cannot("%s cannot be read: %s" % (a.tx_file, e))
        else:
            tx = fetch(a.api or NETWORKS[block["network"]][1], a.txid)
        summary = prove(block, a.txid, tx, tpl, say)
    except Cannot as e:
        print("CANNOT CHECK: %s" % e, flush=True)
        return 2
    except Fail as e:
        say("FAIL", str(e))
        print("NOT PROVEN: this campaign is not what its constants say.", flush=True)
        return 1
    print("PROVEN: one vault, launched OPEN with the page's settings, running the published contracts.", flush=True)
    for line in summary:
        print("  " + line, flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
