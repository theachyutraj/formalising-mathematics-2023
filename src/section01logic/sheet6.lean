/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/

-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.

variables (P Q R S : Prop)

example : P → P ∨ Q :=
begin
  intro p, left, exact p,
end

example : Q → P ∨ Q :=
begin
  intro q, right, exact q,
end

example : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  intros h j k,
  cases h with p q,
  exact j p,
  exact k q,
end

-- symmetry of `or`
example : P ∨ Q → Q ∨ P :=
begin
  intro h,
  cases h with p q,
  right, exact p,
  left, exact q,
end

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) := by cc

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  intros h j k,
  cases k with p q,
  left, exact h p,
  right, exact j q,
end

example : (P → Q) → P ∨ R → Q ∨ R :=
begin
  intros h j,
  cases j with p r,
  left, exact h p,
  right, exact r,
end

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by cc

-- de Morgan's laws
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=  ⟨ λ h, ⟨ λ p, h (or.intro_left _ p), λ q, h (or.intro_right _ q)⟩, λ h pq, or.elim pq h.1 h.2 ⟩ 

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  split,
  repeat {rw ← imp_false},
  intro h,
  
  sorry
end
