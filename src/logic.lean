
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro h,
  intro hp,
  exact hp h,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  by_cases p : P,
  intro h,
  exact p,
  intro h,
  exfalso,
  exact h p,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  by_cases p : P,
  intro h,
  exact p,
  intro h,
  exfalso,
  exact h p,
  intro h,
  intro hp,
  exact hp h,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro hpq,
  cases hpq with p q,
  right,
  exact p,
  left,
  exact q,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro hpq,
  cases hpq with p q,
  split,
  exact q,
  exact p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro h,
  intro p,
  cases h with np q,
  exfalso,
  exact np p,
  exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro h,
  intro hnp,
  cases h with p q,
    exfalso,
    exact hnp p,
    
    exact q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros h nq np,
  have q : Q := h np,
  exact nq q,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro h,
  by_cases q : Q,
  intro p,
  exact q,
  intro p,
  have np : ¬P := h q,
  exfalso,
  exact np p,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intros h nq np,
  have q : Q := h np,
  exact nq q,
  intro h,
  by_cases q : Q,
  intro p,
  exact q,
  intro p,
  have np : ¬P := h q,
  exfalso,
  exact np p,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P ∨ ¬P)  :=
begin
  intro h,
  apply h,
  right,
  intro p,
  apply h,
  left,
  exact p,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro h,
  intro np,
  apply np,
  apply h,
  intro p,
  exfalso,
  exact np p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P ∨ Q → ¬(¬P ∧ ¬Q)  :=
begin
  intro h,
  intro nh,
  cases nh with np nq,
  cases h with p q,
  exact np p,
  exact nq q,
end

theorem conj_as_negdisj :
  P ∧ Q → ¬(¬P ∨ ¬Q)  :=
begin
  intro h,
  intro nh,
  cases h with p q,
  cases nh with np nq,
  exact np p,
  exact nq q,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P ∨ Q) → (¬P ∧ ¬Q)  :=
begin
  intro h,
  split,
  intro p,
  apply h,
  left,
  exact p,
  intro q,
  apply h,
  right,
  exact q,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P ∨ Q)  :=
begin
  intro h,
  intro nh,
  cases h with np nq,
  cases nh with p q,
  exact np p,
  exact nq q,
end

theorem demorgan_conj :
  ¬(P ∧ Q) → (¬Q ∨ ¬P)  :=
begin
  intro h,
  by_cases p : P,
  left,
  intro q,
  apply h,
  split,
  exact p,
  exact q,
  right,
  exact p,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P ∧ Q)  :=
begin
  intro h,
  intro nh,
  cases nh with p q,
  cases h with nq np,
  exact nq q,
  exact np p,
end

theorem demorgan_conj_law :
  ¬(P ∧ Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  intro hpq,
  by_cases p : P,
  left,
  intro q,
  apply hpq,
  split,
  exact p,
  exact q,
  right,
  exact p,

  intro h,
  intro nh,
  cases nh with p q,
  cases h with nq np,
  exact nq q,
  exact np p,

end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  intro h,
  split,
  intro p,
  apply h,
  left,
  exact p,
  intro q,
  apply h,
  right,
  exact q,
  intro h,
  intro hpq,
  cases h with np nq,
  cases hpq with p q,
  exact np p,
  exact nq q,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  :=
begin
  intro h,
  cases h with p q_or_r,
  cases q_or_r with q r,
  
  left,
  split,
  exact p,
  exact q,

  right,
  split,
  exact p,
  exact r,
end

theorem distr_conj_disj_converse :
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  :=
begin
  intro h,
  split,
  
  cases h with pq pr,
  cases pq with p q,
  exact p,
  cases pr with p r,
  exact p,

  cases h with pq pr,
  cases pq with p q,
  left,
  exact q,

  cases pr with p r,
  right,
  exact r,
end

theorem distr_disj_conj :
  P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  :=
begin
  intro h,
  split,
  
  cases h with p q_and_r,
  left,
  exact p,
  cases q_and_r with q r,
  right,
  exact q,
  
  cases h with p q_and_r,
  left,
  exact p,
  cases q_and_r with q r,
  right,
  exact r,
end

theorem distr_disj_conj_converse :
  (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  :=
begin
  intro h,
  cases h with p_or_q p_or_r,
  cases p_or_q with p q,
  left,
  exact p,
  cases p_or_r with p r,
  left,
  exact p,
  right,
  split,
  exact q,
  exact r,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P ∧ Q) → R) → (P → (Q → R))  :=
begin
  intro h,
  intro p,
  intro q,
  apply h,
  split,
  exact p,
  exact q,
end

theorem uncurry_prop :
  (P→ (Q → R)) → ((P ∧ Q) → R)  :=
begin
  intro h,
  intro hpq,
  cases hpq with p q,
  apply h,
  exact p,
  exact q,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro h,
  exact h,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P ∨ Q)  :=
begin
  intro h,
  left,
  exact h,
end

theorem weaken_disj_left :
  Q → (P ∨ Q)  :=
begin
  intro h,
  right,
  exact h,
end

theorem weaken_conj_right :
  (P ∧ Q) → P  :=
begin
  intro h,
  cases h with p q,
  exact p,
end

theorem weaken_conj_left :
  (P ∧ Q) → Q  :=
begin
  intro h,
  cases h with p q,
  exact q,
end

theorem conj_idempot :
  (P ∧ P) ↔ P :=
begin
  split,
  intro hpp,
  cases hpp with p p,
  exact p,
  intro hp,
  split,
  exact hp,
  exact hp,
end

theorem disj_idempot :
  (P ∨ P) ↔ P  :=
begin
  split,
  intro hpp,
  cases hpp with p p,
  exact p,
  exact p,
  intro hp,
  left,
  exact hp,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro h,
  intro a,
  intro pa,
  apply h,
  existsi a,
  exact pa,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro h,
  intro e,
  cases e with x px,
  have nx : ¬P x := h x,
  exact nx px,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro h,
  by_contra hc,
  apply h,
  intro x,
  by_contra p,
  apply hc,
  existsi x,
  exact p,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro h,
  intro n,
  cases h with x npx,
  apply npx,
  have px : P x := n x,
  exact px,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  exact demorgan_forall U P,
  exact demorgan_forall_converse U P,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  exact demorgan_exists U P,
  exact demorgan_exists_converse U P,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro h,
  intro n,
  cases h with x hx,
  have nx : ¬P x := n x,
  exact nx hx,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro h,
  intro e,
  cases e with x hx,
  apply hx,
  have px : P x := h x,
  exact px,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro h,
  intro x,
  by_contra hb,
  apply h,
  existsi x,
  exact hb,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro h,
  cases h with x pq,
  cases pq with px qx,
  split,
  existsi x,
  exact px,
  existsi x,
  exact qx,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro h,
  cases h with x pq,
  cases pq with px qx,
  left,
  existsi x,
  exact px,
  right,
  existsi x,
  exact qx,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro h,
  cases h with exp exq,
  cases exp with x px,
  existsi x,
  left,
  exact px,
  cases exq with x qx,
  existsi x,
  right,
  exact qx,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro h,
  split,
  intro x,
  have pq : P x ∧ Q x := h x,
  cases pq with px qx,
  exact px,
  intro x,
  have pq : P x ∧ Q x := h x,
  cases pq with px qx,
  exact qx,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro h,
  cases h with xpx xqx,
  intro x,
  split,
  have px : P x := xpx x,
  exact px,
  have qx : Q x := xqx x,
  exact qx,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro h,
  intro x,
  cases h with xpx xqx,
  have px : P x := xpx x,
  left,
  exact px,
  have qx : Q x := xqx x,
  right,
  exact qx,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
