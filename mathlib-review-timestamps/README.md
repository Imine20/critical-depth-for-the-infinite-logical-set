These receipts bind the **portable r3 release**, whose canonical 2,276-byte,
20-file manifest has SHA-256
`99617c524af8d44dc5f823275671e57e9a978b2b7be9f0dd827960dd0bf6e7ee`.
The manifest contains SHA-256, byte length and repository-relative path for
each primary file. Timestamp receipts are excluded to avoid self-reference.
R1 and r2 receipts bind different manifests and do not cover r3 merely because
some source files are unchanged.

The primary r3 snapshot is published at
[commit 9fda1b1ef1b95495b929a90797baf9ea4a045250](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/commit/9fda1b1ef1b95495b929a90797baf9ea4a045250).
The publication check matched all 20 remote file bytes and lengths. The
timestamp manifest binds those bytes; a Git date is not timestamp evidence.

The r3 standalone ZIP is 609,522 bytes, SHA-256
`b4f45ce84875e43921a536cb69637544bddead761044bd1693f113bdfb97c4ad`.
The Lean source remains SHA-256
`85af30d2f9cdf217a729c004d7af0ad67f87b4a821eb28e38ae70dfec840dfd8`.
The RFC 3161 signature, request/file binding, nonce, certificate chain and
critical timestamping EKU passed the recorded checks. The token's signed time
is **2026-11-01 12:08:21 UTC**. Certificate revocation is **UNCHECKED**.
OTS obtained two actual selected-calendar replies. The later upgrade still
reported pending confirmation: **Bitcoin confirmation is PENDING**.

This directory contains only portable cryptographic evidence:
the canonical manifest; DER request, response and token; public certificate
material and fingerprints; rendered query/reply and certificate fields;
verification results using relative filenames; binary OTS receipts; and a
whitelisted summary. It does not contain host paths, stderr configuration
messages, OS/package dumps, command vectors, process identifiers, resource
receipts or raw client summaries. Canonical copies preserve the original bytes.
`SHA256SUMS` covers all public-copy files except itself.

The r3 nonce is `0x3687F0075F562643`, policy is `2.16.840.1.114412.7.1`,
and token serial is `0x3227BB7CE07A4D7305FEB47F5508297C`. The imprint is
the manifest's SHA-256 above. The selected endpoint was
`http://timestamp.digicert.com`; the query transmitted the imprint and nonce,
not file contents. The signer is DigiCert SHA256 RSA4096 Timestamp Responder
2026 1. The accepted root is DigiCert Trusted Root G4, DER SHA-256
`552f7bdcf1a7af9e6ce672017f4f12abf77240c78e761ac203d1d9d20ac89988`.

Both timestamp verification outputs read `Verification: OK`; the separate
signer-chain check also passed. A nonfatal warning arose because the untrusted
certificate stack includes the signer as well as issuer certificates. No
warning-free or revocation-checked result is claimed. The signed time is the
TSA's assertion, subject to trust in its clock; it is not a synchronized
measurement against another system's clock.

Reproduce the saved RFC checks with OpenSSL 3 from this receipt directory:

```sh
sha256sum -c SHA256SUMS
cd rfc3161
openssl ts -query -in release-manifest.tsq -text
openssl ts -reply -in release-manifest.tsr -text
openssl ts -verify -queryfile release-manifest.tsq -in release-manifest.tsr -CAfile trusted-root.pem -untrusted response-certificates.pem
openssl ts -verify -data ../release-manifest.txt -in release-manifest.tsr -CAfile trusted-root.pem -untrusted response-certificates.pem
openssl verify -show_chain -purpose timestampsign -no-CApath -no-CAstore -CAfile trusted-root.pem -untrusted response-certificates.pem actual-signer.pem
openssl x509 -in actual-signer.pem -noout -ext extendedKeyUsage
openssl x509 -in trusted-root.pem -outform DER | openssl dgst -sha256
cd ..
```

The root used for validation was checked against an independent trusted
source. A root supplied beside a receipt does not establish trust by itself:
compare its fingerprint with your own trusted source. Signature and chain
acceptance alone do not imply an OCSP/CRL check.

The OTS client was official `opentimestamps` `0.4.9`, with source-commit
metadata pin `36e27fca500273a63e013fff62d963357e882a27`. This value is
package metadata, not a claim of independently verified local Git state.
The helper sent 32-byte nonce-blinded commitments,
`SHA256(file_digest || fresh_16_byte_nonce)`, not file contents.
It selected `https://a.pool.opentimestamps.org`,
`https://b.pool.opentimestamps.org` and `https://a.pool.eternitywall.com`.

There were five submissions in two bounded rounds. Bob replied in round one;
Finney replied in round two. Alice returned `AggregateError` in both rounds.
Two distinct selected URLs replied; this does not establish independent
operator identities. The actual pending URIs are:

- `https://bob.btc.calendar.opentimestamps.org`
- `https://finney.calendar.eternitywall.com`

The initial 219-byte receipt contains Bob only and was preserved unchanged.
The 446-byte merged receipt contains Bob and Finney. The upgrade used a copy
of the merged receipt and left it unchanged; both calendars still reported
`Pending confirmation in Bitcoin blockchain`. No Bitcoin block-header
attestation, block height or Bitcoin-verification attempt was recorded.

| Receipt | Bytes | SHA-256 |
| --- | ---: | --- |
| `ots/release-manifest.txt.initial.ots` | 219 | `08a11a234442edc8265018e448d03813c33222f6329f469325cadf72e423c43b` |
| `ots/release-manifest.txt.merged.ots` | 446 | `ff29d4e8d0b0aee8f120d9272e189fd76d41e146a553c01695173b77336bc140` |
| `ots/release-manifest.txt.upgraded.ots` | 446 | `ff29d4e8d0b0aee8f120d9272e189fd76d41e146a553c01695173b77336bc140` |

With an installed official JavaScript OTS CLI, inspect these receipts with
`node "$OTS_CLI" info ots/release-manifest.txt.merged.ots`, where `OTS_CLI`
names the client's `ots-cli.js`. Receipt inspection and calendar acceptance
are not completed Bitcoin verification. Future upgrade checks should preserve
the initial and merged receipts and operate on another copy.

Check the 20 primary rows against a matching r3 checkout or export from this
receipt directory:

```sh
python3 - .. <<'PY'
import hashlib
import pathlib
import sys

root = pathlib.Path(sys.argv[1]).resolve()
rows = pathlib.Path('release-manifest.txt').read_text(encoding='utf-8').splitlines()
assert len(rows) == 20
seen = set()
for row in rows:
    digest, size, name = row.split('\t', 2)
    relative = pathlib.PurePosixPath(name)
    assert not relative.is_absolute() and '..' not in relative.parts
    assert name not in seen
    seen.add(name)
    path = root.joinpath(*relative.parts).resolve()
    assert root == path or root in path.parents
    payload = path.read_bytes()
    assert len(payload) == int(size), name
    assert hashlib.sha256(payload).hexdigest() == digest, name
print('20 r3 file hashes and lengths match')
PY
```

Timestamps concern exact bytes under the stated trust boundaries. They do not
establish authorship, originality, legal qualification, mathematical correctness
or author semantic approval. The timestamp evidence is published separately
from the primary commit above.
