# Verified List Algorithm

A formal verification project in Lean 4 that proves the correctness of list reversal algorithms.

This project was created as a learning exercise in theorem proving and formal verification using Lean 4. The goal is to verify that different implementations of list reversal produce the same result and satisfy their intended specifications.

---


## Definitions

The project defines multiple list reversal functions.

### Naive Reverse

A simple recursive implementation of list reversal.

```lean
def myReverse : List α → List α
```

---

### Tail-Recursive Reverse

An accumulator-based implementation.

```lean
def revAux : List α → List α → List α
```

---

### Fast Reverse

A reverse function built using the auxiliary accumulator function.

```lean
def fastReverse : List α → List α
```

---

## Verified Properties

The project formally proves several properties of lists and list reversal.

### Append Identity

```text
xs ++ [] = xs
```

---

### Correctness of Auxiliary Reverse

```text
revAux xs acc =
myReverse xs ++ acc
```

This theorem connects the accumulator-based implementation to the specification.

---

### Correctness of Fast Reverse

```text
fastReverse xs = myReverse xs
```

This proves that the optimized tail-recursive implementation behaves exactly like the original definition.

---

## Example

For a list

```text
[1,2,3,4,5]
```

both implementations produce

```text
[5,4,3,2,1]
```

The proofs establish that this equality holds for all lists, not just examples.

---



## Author

Shridhar Naik

Independent Lean 4 formal verification project.