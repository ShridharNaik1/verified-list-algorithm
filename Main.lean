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

theorem reverse_reverse (xs : List Nat) : myReverse (myReverse xs) = xs := by
    induction xs with
    | nil =>
       rfl
    | cons x xs ih =>
       rw [myReverse, reverse_append, ih, reverse_singleton]
       rfl

theorem reverse_cons (x : Nat) (xs : List Nat) : myReverse (x :: xs) = myReverse xs ++ [x] := by
    rfl

theorem reverse_length (xs : List Nat) : (myReverse xs).length = xs.length := by
    induction xs with
    | nil =>
       rfl
    | cons x xs ih =>
       rw [myReverse, List.length_append, List.length_singleton, ih]
       rfl

theorem append_length (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length := by
    induction xs with
    | nil =>
       rw [List.nil_append, List.length_nil, Nat.zero_add]
    | cons x xs ih =>
       rw [List.cons_append, List.length_cons, ih, List.length_cons, Nat.succ_add]
