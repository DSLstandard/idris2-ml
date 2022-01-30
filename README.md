# idris2-ml

pure idris2 type dependent machine learning library implementation

not for practical use

- `src/Backprop`: heterogeneous backpropagation
- `src/Linear`: linear algebra
- `src/Linear/Backprop`: linear algebra backpropagation
- `src/NN`: neural network constructs
- `src/Examples`: use REPL to load them, takes a ton of time (~15 seconds on my Gentoo) if uses of `Nat` in compile time (e.g. `Dense (28\*28\*1) 10 Double`)

will split them later
