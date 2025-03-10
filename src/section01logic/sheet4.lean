/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `split`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : P ∧ Q → P := λ h, h.1
-- begin
--   sorry
-- end

example : P ∧ Q → Q := λ h, h.2
-- begin
--   intro h, exact h.2,
-- end

example : (P → Q → R) → (P ∧ Q → R) := 
begin
  intros h j, 
  apply h, exact j.1, exact j.2,
end

example : P → Q → P ∧ Q :=
begin
  intros p q,
  split,
  exact p, exact q,
end

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P :=
begin
  intro h, split, exact h.2, exact h.1,
end

example : P → P ∧ true :=
begin
  intro p, split, exact p, triv,
end

example : false → P ∧ false :=
begin
  intro f, split, exfalso, exact f, exact f,
end

/-- `∧` is transitive -/
example : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  intros h j,
  split,
  exact h.1,
  exact j.2,
end

example : ((P ∧ Q) → R) → (P → Q → R) :=
begin
  intros h p q,
  apply h,
  split,
  exact p, 
  exact q,
end



