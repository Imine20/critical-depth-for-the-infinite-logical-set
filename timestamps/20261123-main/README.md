# November 23 manuscript timestamps

The [PDF](../../manuscript/MAIN.pdf) was built with TeX Live pdfLaTeX and BibTeX from the [TeX](../../manuscript/MAIN.tex) and [bibliography](../../manuscript/depth.bib) committed in [`a218706`](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/commit/a2187060a10e5d5664f7948dcb6df4552fe19213). It has 20 pages. All references resolved and the three figures appear on pages 3–5.

| Signed input | SHA-256 | DigiCert time (UTC) |
| --- | --- | --- |
| [`manuscript/MAIN.pdf`](../../manuscript/MAIN.pdf) | `da4bc5aea08c40edf7595f9b357797d6896acf2eddd59073e8280736bbf36f5a` | 2026-11-23 12:28:12 |
| [`PAYLOAD.json`](PAYLOAD.json) | `ee8fe2a7a2e9a5496153d8b9793fcb23dfe5f9fee5d6b0c54e80e49bae8f99cc` | 2026-11-23 12:28:13 |

The manifest binds the exact byte lengths and SHA-256 digests of the PDF, TeX and bibliography. Both tokens use SHA-256, policy `2.16.840.1.114412.7.1` and distinct nonces. The DER requests and unmodified replies are stored as `.tsq` and `.tsr` files. [Receipt metadata](RECEIPT.json) · [Verification output](VERIFICATION.txt)

The requests went to DigiCert's [documented RFC 3161 endpoint](https://knowledge.digicert.com/general-information/rfc3161-compliant-time-stamp-authority-server). The certificate used as a trust anchor came from the Windows trusted-root store, and its SHA-256 fingerprint matched the [independently published DigiCert Trusted Root G4 fingerprint](https://knowledge.digicert.com/general-information/digicert-trusted-root-authority-certificates). The responder had the critical Time Stamping extended key usage. Both signed CRLs in [`crls.pem`](crls.pem) were checked at each signed time. The retained CRLs show the revocation data available for these signed times.

## Verify from the repository root

First confirm the SHA-256 fingerprint of the trust anchor through your own trust store or the independently published fingerprint linked above. The expected value is `552f7bdcf1a7af9e6ce672017f4f12abf77240c78e761ac203d1d9d20ac89988`.

~~~sh
e=timestamps/20261123-main
openssl x509 -in "$e/trusted-root.pem" -noout -sha256 -fingerprint
openssl x509 -in "$e/signer.pem" -noout -ext extendedKeyUsage

for entry in "MAIN.pdf 1795436892 manuscript/MAIN.pdf" \
             "PAYLOAD.json 1795436893 $e/PAYLOAD.json"; do
  set -- $entry
  stem=$1
  epoch=$2
  input=$3
  openssl ts -verify -attime "$epoch" -queryfile "$e/$stem.tsq" \
    -in "$e/$stem.tsr" -CAfile "$e/trusted-root.pem" -untrusted "$e/issuer.pem"
  openssl ts -verify -attime "$epoch" -data "$input" \
    -in "$e/$stem.tsr" -CAfile "$e/trusted-root.pem" -untrusted "$e/issuer.pem"
  openssl verify -attime "$epoch" -purpose timestampsign \
    -CAfile "$e/trusted-root.pem" -untrusted "$e/issuer.pem" \
    -CRLfile "$e/crls.pem" -crl_check_all "$e/signer.pem"
done

python3 - <<'PY'
from hashlib import sha256
from pathlib import Path
import json

manifest = Path("timestamps/20261123-main/PAYLOAD.json")
for entry in json.loads(manifest.read_bytes())["files"]:
    data = Path(entry["path"]).read_bytes()
    if len(data) != entry["bytes"] or sha256(data).hexdigest() != entry["sha256"]:
        raise SystemExit(f"Byte mismatch for {entry['path']}")
    print(f"Verified {entry['path']}")
PY
~~~

The verification run additionally extracted each token's actual CMS signer and checked that its fingerprint matches `signer.pem`. The November 15 [release evidence](https://github.com/Imine20/critical-depth-for-the-infinite-logical-set/blob/5dfbf322eb5b59f6ba44d860691638d0ec2b9c5c/CURRENT_VERSION.json) retains its original scope. These timestamps cover file bytes and give no new Lean execution evidence.
