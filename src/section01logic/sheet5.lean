/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/

variables (P Q R S : Prop)

example : P ↔ P :=
begin
  split,
  intro p, exact p,
  cc,
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
  intro h,
  split, exact h.2,
  exact h.1,
end

example : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split,
  intro h, split, exact h.2, exact h.1,
  intro h, split, exact h.2, exact h.1,
end

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intros h j,
  split, intro p, exact j.1 (h.1 p),
  intro r, exact h.2 (j.2 r),
end

example : P ∧ Q ↔ Q ∧ P :=
begin
  split,
  {intro h,
  split,
  exact h.2,
  exact h.1},
  {intro h,
  split,
  exact h.2, 
  exact h.1},
end

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  split,
  intro h,
  split,cc,cc,cc,
end

example : P ↔ (P ∧ true) :=
begin
  split,
  intro p, split, exact p,triv,
  intro h, exact h.1,
end

example : false ↔ (P ∧ false) :=
begin
  split,
  intro f,
  split,
  exfalso,
  exact f, exact f,
  intro h,
  exact h.2,
end

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by cc

example : ¬ (P ↔ ¬ P) :=
begin
  rw ← imp_false, intro h, rw ← imp_false at h, cc,
end
