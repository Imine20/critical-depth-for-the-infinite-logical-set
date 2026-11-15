# Update_branch RFC 3161 timestamp evidence

DigiCert issued one token for the [published TeX](../../manuscript/Update_branch.tex)
and one for the [release input manifest](../../verification-runs/update-branch/INPUTS.sha256.tsv).

| Input | UTC genTime | SHA-256 |
| --- | --- | --- |
| Published `Update_branch.tex` | 2026-11-15T02:33:19Z | `bbdbefefd9f5b0fc8db465dbe679e885a64f7d6b063b5537dc29888572564e22` |
| Release input manifest | 2026-11-15T02:39:12Z | `9d698ce8a6dec815b43d5b1ebb449d04717acf0fd2e46a6ac93e0e475d7b2e8b` |

The manifest contains 360 repository-relative paths with the canonical Git blob byte
lengths and SHA-256 hashes. It includes the manuscript, all 346 project Lean
modules in the full replay, the dependency locks, the verifier, the release
correspondence and the cited audit records.

Both requests and responses are preserved as DER files. OpenSSL 3.2.4 returned
`Verification: OK` for each request and nonce and for each input file. The
response signer certificates have the critical timeStamping extended key
usage. Verification used DigiCert Trusted Root G4 from the Windows trust
store. Its DER SHA-256 fingerprint is
`552f7bdcf1a7af9e6ce672017f4f12abf77240c78e761ac203d1d9d20ac89988`.
Cross-check this fingerprint against a trusted store before using the
bundled root. The [provider's documentation](https://knowledge.digicert.com/general-information/rfc3161-compliant-time-stamp-authority-server)
lists the endpoint and issuer. Signed CRLs were checked at genTime and again
at verification time. [RECEIPT.json](RECEIPT.json) records the policy, serials,
nonces and checksums. [VERIFICATION.txt](VERIFICATION.txt) contains the
verification outcomes.

Run these commands from this directory with OpenSSL:

    openssl ts -verify -queryfile Update_branch.tex.tsq -in Update_branch.tex.tsr -CAfile trusted-root.pem -untrusted intermediate.pem
    openssl ts -verify -data ../../manuscript/Update_branch.tex -in Update_branch.tex.tsr -CAfile trusted-root.pem -untrusted intermediate.pem
    openssl ts -verify -queryfile INPUTS.sha256.tsv.tsq -in INPUTS.sha256.tsv.tsr -CAfile trusted-root.pem -untrusted intermediate.pem
    openssl ts -verify -data ../../verification-runs/update-branch/INPUTS.sha256.tsv -in INPUTS.sha256.tsv.tsr -CAfile trusted-root.pem -untrusted intermediate.pem
    openssl verify -purpose timestampsign -attime 1794709999 -crl_check_all -CRLfile digicert-crls.pem -CAfile trusted-root.pem -untrusted intermediate.pem Update_branch.tex.signer.pem
    openssl verify -purpose timestampsign -attime 1794710352 -crl_check_all -CRLfile digicert-crls.pem -CAfile trusted-root.pem -untrusted intermediate.pem INPUTS.sha256.tsv.signer.pem

The [release record](../../verification-runs/update-branch/RELEASE.md) gives the
manuscript and proof correspondence. The tokens bind the exact input bytes to
the TSA's signed times. OpenTimestamps was omitted at the author's request.
