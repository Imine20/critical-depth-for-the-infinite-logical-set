# Archived dependency-source attempt

The selected current policy is **TRUSTED_PINNED_MATHLIB_CACHE**. The user
explicitly trusts Mathlib and requested that it be referenced rather than
rebuilt or vendored. The root dependency requirement, `lake-manifest.json`
and Lean imports identify the fixed public versions. No dependency source
rebuild is required for the current verification.

The earlier source-closure attempt was stopped safely at the user's request
after 3,343 of 3,699 planned modules. It remains **USER_STOPPED_INCOMPLETE**.
Its initial failed attempt, resume and later user stop retain their separate
historical record; they do not establish a full source-closure PASS.
Unfinished temporary source/output trees and source-build helpers are not
part of the current publication. Their cleanup is separate from checking the
unchanged manuscript, statements and Lean source against the trusted cache.

Follow the [current verification guide](VERIFICATION.md) for the pinned
versions, fresh main-source audit and separate external caller. The
[version index](../VERIFICATION_STATUS.md) and linked run records determine
the actual executed outcome; this note grants no provisional PASS. Author
semantic approval remains separately version-bound, and CAD formalization is
deferred.

The complete preceding public main tree and its original evidence are
preserved under [the archive](../archive/README.md), without promoting their
historical status to current acceptance.
