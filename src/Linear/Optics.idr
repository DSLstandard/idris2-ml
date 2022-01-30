module Linear.Optics

import Control.Optics
import Linear.V

export
as_column : Iso (T [n] a) (T [n] b) (T [n, 1] a) (T [n, 1] b)
as_column = iso (map pure) (map (\[x] => x))

export
as_row : Iso (T [n] a) (T [n] b) (T [1, n] a) (T [1, n] b)
as_row = iso pure (\[x] => x)

export
reshaped : (size : List Nat) -> {auto ns : _} -> {auto prf : prod ns = prod size} -> Iso (T ns a) (T ns b) (T size a) (T size b)
reshaped size = iso (reshape size {ns}) (reshape ns {ns=size} {prf = sym prf})
