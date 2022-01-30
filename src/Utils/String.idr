module Utils.String

import Data.String.Extra

export
show_record : String -> List (String, String) -> String
show_record name x = name <+> " { " <+> (join ", " $ map (\(k, v) => k <+> " = " <+> v) x) <+> " }"
