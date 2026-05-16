def myReverse {α : Type} : List α → List α
| [] => []
| x :: xs => myReverse xs ++ [x]

#eval myReverse [1, 2, 3, 4, 5]
