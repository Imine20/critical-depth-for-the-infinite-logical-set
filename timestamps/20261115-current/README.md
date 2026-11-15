# Current manuscript and publication-input timestamps

DigiCert issued two RFC 3161 tokens for this publication. The first binds the
[unchanged current TeX at its immutable source commit](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/blob/0f0212793b7a911471d9318f554c8c2a9e41fb1a/manuscript/Update_branch.tex).
The second binds [PAYLOAD.json](PAYLOAD.json), whose 699 entries cover the
publication inputs, including the TeX, PDF, mathematical statements, updated
correspondence and entry points, all Lean sources and existing verification
evidence. The PDF is covered through this manifest; it has no separate token.

| Input | Bytes | UTC genTime | SHA-256 |
| --- | ---: | --- | --- |
| `manuscript/Update_branch.tex` | 126168 | 2026-11-15T08:19:28Z | `08452c4636132e06dd9f4757d530c479ef5a17ce02bc070908e90b8c0e896343` |
| `PAYLOAD.json` | 117620 | 2026-11-15T08:19:44Z | `daf4afc98769cf7f1f2d7714a532ce2742ddee86ed73fb3b1d76752506e1178b` |

## Binding and scope

[CURRENT_VERSION.json](../../CURRENT_VERSION.json) is the latest entry point.
It binds this manifest, both original requests and responses, the verification
record, certificate material and current publication documents. Its enclosing
Git commit binds the version record itself. PAYLOAD excludes CURRENT_VERSION
and this timestamp directory to avoid a circular hash dependency. The final
Git tree is checked separately for complete coverage outside these exclusions.
The signed manifest is not a timestamp of the later responses or version record.

The earlier [Update_branch timestamp set](../update-branch/README.md) still
binds the pre-alignment manuscript and its old 360-entry manifest. All old
tokens, requests, certificates, verification records and input-manifest bytes
were preserved. The two historical documentation entry points now identify
the immutable old manuscript and explain how to verify its original bytes.
[HISTORICAL_CHECK.json](HISTORICAL_CHECK.json) records the successful command
checks; its old CRL checks apply to the original token generation times.

No mathematical text, Lean source, dependency pin or proof replay result changed
in this timestamp refresh. The existing 346-module / 19-audit replay remains
bound to the same proof inputs; it was not run again. A timestamp can establish
that the bound bytes existed by the TSA's signed time, subject to trust in the
TSA and its clock. It does not establish authorship or mathematical correctness.
OpenTimestamps was omitted at the author's request.

## Verification

The [receipt](RECEIPT.json) records each input, nonce, policy, serial, signer and
verification outcome. [VERIFICATION.txt](VERIFICATION.txt) contains the OpenSSL
output from checks against frozen byte-identical copies. Both request and file
verification succeeded, as did signer-chain and signed-CRL checks at genTime and
at the recorded verification time. The actual response signer is DigiCert SHA256
RSA4096 Timestamp Responder 2026 1, with critical timeStamping extended key usage.

The self-signed DigiCert Trusted Root G4 was read independently from the Windows
LocalMachine Root store before requests were sent. Its DER SHA-256 is
`552f7bdcf1a7af9e6ce672017f4f12abf77240c78e761ac203d1d9d20ac89988`.
Cross-check this fingerprint against an independent trusted store before using
the bundled root. OpenSSL 3.5.9 came from the hash-verified official Git for
Windows distribution; [TOOLCHAIN.json](TOOLCHAIN.json) records its provenance.
The [DigiCert documentation](https://knowledge.digicert.com/general-information/rfc3161-compliant-time-stamp-authority-server)
identifies the endpoint and current certificate chain. The transmitted payload
was a SHA-256 imprint, fresh nonce and certificate-request flag, not file contents.

Run the following from this directory with OpenSSL. The digest command explicitly
identifies the stamped TeX even if a later branch changes the manuscript path.

~~~sh
openssl ts -verify -queryfile Update_branch.tex.tsq -in Update_branch.tex.tsr -CAfile trusted-root.pem -untrusted intermediate.pem
openssl ts -verify -digest 08452c4636132e06dd9f4757d530c479ef5a17ce02bc070908e90b8c0e896343 -in Update_branch.tex.tsr -CAfile trusted-root.pem -untrusted intermediate.pem
openssl ts -verify -queryfile PAYLOAD.json.tsq -in PAYLOAD.json.tsr -CAfile trusted-root.pem -untrusted intermediate.pem
openssl ts -verify -data PAYLOAD.json -in PAYLOAD.json.tsr -CAfile trusted-root.pem -untrusted intermediate.pem
openssl verify -purpose timestampsign -attime 1794730768 -crl_check_all -CRLfile digicert-crls.pem -CAfile trusted-root.pem -untrusted intermediate.pem Update_branch.tex.signer.pem
openssl verify -purpose timestampsign -attime 1794730784 -crl_check_all -CRLfile digicert-crls.pem -CAfile trusted-root.pem -untrusted intermediate.pem PAYLOAD.json.signer.pem
~~~

To check the actual publication files, use a checkout of the Git commit that
contains this timestamp set, then run from the repository root:

~~~sh
python -B scripts/check_current_version.py
openssl ts -verify -data manuscript/Update_branch.tex -in timestamps/20261115-current/Update_branch.tex.tsr -CAfile timestamps/20261115-current/trusted-root.pem -untrusted timestamps/20261115-current/intermediate.pem
~~~

The Python command checks raw-byte bindings, manifest coverage and recorded
outcomes; it does not verify TSA signatures. The OpenSSL command checks the
file itself. If checking this stamped manuscript from a later checkout, recover the
exact Git blob from the immutable source commit linked above using the binary
extraction method in the [historical instructions](../update-branch/README.md),
with this source commit, byte length and digest substituted.

The bundled CRLs support the recorded verification times. A check of present-day
revocation status requires current CRLs from the URLs in RECEIPT.json; do not
treat an expired CRL as current evidence. Certificate validity can likewise
require evaluating a historical token at its signed time.
