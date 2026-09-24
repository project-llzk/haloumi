; TEMPORARY BACKUP: port this legacy PCL prelude into a downstream semantic prelude.
; Spread prelude
; When invoking Picus declare these modules as deterministic
(begin-module Spread)
(input i)
(output o)
(end-module)
(begin-module Unspread)
(input i)
(output o)
(end-module)
; End of Spread prelude
