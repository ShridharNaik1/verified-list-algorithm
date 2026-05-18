def myReverse {α : Type} : List α → List α
| [] => []
| x :: xs => myReverse xs ++ [x]

#eval myReverse [1, 2, 3, 4, 5]

theorem reverse_nil : myReverse ([] : List Nat) = [] := by rfl

theorem reverse_singleton (x : Nat) : myReverse [x] = [x] := by rfl

theorem reverse_append_nil (xs : List Nat) : myReverse (xs ++ []) = myReverse xs := by
 rw [List.append_nil]

theorem reverse_append (xs ys : List Nat) : myReverse (xs ++ ys) = myReverse ys ++ myReverse xs := by
    induction xs with
    | nil =>
       rw [List.nil_append, myReverse, List.append_nil]
    | cons x xs ih =>
       rw [List.cons_append, myReverse, ih, List.append_assoc, myReverse]
