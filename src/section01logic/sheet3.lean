/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2023/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : ¬ true → false :=
begin
  intro t, rw not_true at t, exact t,
end

example : false → ¬ true :=
begin
  intro f, exfalso, exact f,
end

example : ¬ false → true :=
begin
  rw ← imp_false, intros h, by_contra j, rw not_true at j, exact j,
end

example : true → ¬ false :=
begin
  rw ← imp_false, intros t f, exact f,
end

example : false → ¬ P :=
begin
  rw ← imp_false, intros f p, exact f,
end

example : P → ¬ P → false :=
begin
  rw ← imp_false, intros p h, exact h p,
end

example : P → ¬ (¬ P) :=
begin
  rw not_not, intro p, exact p,
end

example : (P → Q) → (¬ Q → ¬ P) :=
begin
  repeat {rw ← imp_false}, intros h j p, exact j (h p),
end

example : ¬ ¬ false → false :=
begin
  repeat {rw ←imp_false },
  intros h, apply h, intro f, exact f,
end

example : ¬ ¬ P → P :=
begin
  intros nnp, rw not_not at nnp, exact nnp,
end

example : (¬ Q → ¬ P) → (P → Q) :=
begin
  intros h p, 
  by_cases hq:Q,
  exact hq,
  exact absurd p (h hq),
  -- exfalso, 
  -- exact h hq p,

  -- by_contra hq,
  -- exact h hq p,/
end