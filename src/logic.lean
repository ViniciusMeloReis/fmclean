
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intros h h2,
  apply h2,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro h,
  by_cases h : P,
  assumption,
  contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  intro h,
  by_cases h: P,
  assumption,
  contradiction,
  intros h h2,
  contradiction,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro h,
  cases h with hp hq,
  right,
  assumption,
  left,
  assumption,


  
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
intro h,
cases h with hp hq,
split,
assumption,
assumption,

  
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro hpq,
  cases hpq with np nq,
  contradiction,
  intro h,
  assumption,

end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro hpq,
  cases hpq with h1 h2,
  contradiction,
  intro h,
  assumption,


end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro hpq,
  intro h1,
  intro h2,
  have hqq : Q := hpq h2,
  contradiction,
 

 
  
  
  

end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro hqp,
  intro h1,
  by_cases h2 : Q,
  exact h2,
  have hpp :  ¬P := hqp h2,
  contradiction,
  
  
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intro hpq,
  intro h1,
  intro h2,
  have hqq : Q := hpq h2,
  contradiction,
   intro hpq,
  intro h1,
  by_cases h2 : Q,
  exact h2,
  have hpp :  ¬P := hpq h2,
  contradiction,


  
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro h,
  have hpp : P ∨ ¬P,
  right,
  intro h1,
  have hppp: P ∨ ¬P,
  left,
  assumption,
  apply h hppp,
  apply h hpp,


  
  
  
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
    intros hp,
    intro h1,
    have hpp : (P → Q),
    intro h2,
    contradiction,
    have hppp : P := hp hpp,
    contradiction,
  
  
  
  
 
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro hp,
  intro h1,
  cases h1,
  cases hp,
  contradiction,
  contradiction,


  


end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro hpq,
  intro h1,
  cases hpq,
  cases h1,
  contradiction,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro hpq,
  split,
  intro hp,
  have hqp : P∨Q,
  left,
  assumption,
  contradiction,
  intro hqq,
  have hqqq : P∨Q,
  right,
  assumption,
  contradiction,
  

  
  

  
  
  
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro hpq,
  intro hqp,
  cases hpq,
  cases hqp,
  contradiction,
  contradiction,

  
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro hpq,
  by_cases P,
  left,
  by_contradiction q,
  have hp : P∧Q,
  split,
  assumption,
  assumption,
  contradiction,
  right,
  assumption,

  
 
  
  

end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro hqp,
  intro hpq,
  cases hpq,
  cases hqp,
  contradiction,
  contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
      split, 
  exact demorgan_conj P Q,
  exact demorgan_conj_converse P Q,
  

  

end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  intro hpq,
  split,
  intro hp,
  have hq : P∨Q,
    left,
    assumption,
  contradiction,
  intro hq,
  have hqq : P∨Q,
    right,
    assumption,
  contradiction,
  intros hpq,
  intro hqp,
  cases hpq,
  cases hqp,
  contradiction,
  contradiction,

end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
 intro hpqr,
  cases hpqr,
  cases hpqr_right,
  left,
  split,
  assumption,
  assumption,
  right,
  split,
  assumption,
  assumption,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro hpqr,
  split,
  cases hpqr,
  cases hpqr,
  assumption,
  cases hpqr,
  assumption,
  cases hpqr,
  left,
  cases hpqr,
  assumption,
  right,
  cases hpqr,
  assumption,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro hpqr,
  cases hpqr,
  split,
  left,
  apply hpqr,
  left,
  apply hpqr,
  cases hpqr,
  split,
  right,
  apply hpqr_left,
  right,
  apply hpqr_right,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
    intro hpqr,
  cases hpqr,
  cases hpqr_left,
  cases hpqr_right,
  left,
  assumption,
  left,
  assumption,
  cases hpqr_right,
  left,
  assumption,
  right,
  split,
  assumption,
  assumption,
  
    
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro hpqr,
  intro hp,
  intro hq,
  have hpq:P∧Q,
  split,
  assumption,
  assumption,
  have hr : R := hpqr hpq,
  assumption,

  
  
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro hpqr,
  intro hpq,
  cases hpq,
  have hr : R := hpqr hpq_left hpq_right,
  assumption,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro hp,
  assumption,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro hp,
  left,
  assumption,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro hq,
  right,
  assumption,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro hpq,
  cases hpq,
  assumption,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro hpq,
  cases hpq,
  assumption,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro hp,
  cases hp,
  assumption,
  intro hpp,
  split,
  assumption,
  assumption,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro hp,
  cases hp,
  assumption,
  assumption,
  intro hpp,
  right,
  assumption,
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
  intro hp,
  intro hpp,
  intro hppp,
  apply hp,
  existsi hpp,
  assumption,

 
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro hp,
  intro hpp,
  cases hpp with hqp hpq,
   have hq : ¬P hqp := hp hqp,
   contradiction,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro hp,
  
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro hp,
  intro hpp,
  cases hp with hqp hpq,
  have hqq : P hqp := hpp hqp,
  contradiction,

end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro hp,
  intro hpp,
  cases hp with hqp hpq,
  exact hpp hqp hpq,
  
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro hp,
  intro hpp,
  cases hpp with hqp hpq,
  have hppp : P hqp := hp hqp,
  contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro hp,
  intro hpp,
  by_cases hq : P hpp,
  assumption,

  
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  ,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  intro hp,
  intro hq,
  cases hp with hpq hqp,
  have hpp : ¬P hpq := hpq hq,
  
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro hp,
  split,
  cases hp with hpq hqp,
  cases hqp,
  existsi hpq,
  exact hqp_left,
  cases hp with hpq hqp,
  cases hqp,
  existsi hpq,
  exact hqp_right,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro h,
  cases h with hp hq,
  cases hq,
  left,
  existsi hp,
  exact hq,
  right,
  existsi hp,
  exact hq,


end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro h,
  cases h with hp hq,
  cases hp with p hpp,
  have hpq : P p ∨ Q p,
  left,
  exact hpp,
  existsi p,
  exact hpq,
  cases hq with q hqq,
  have hpq: P q ∨ Q q,
  right,
  exact hqq,
  existsi q,
  exact hpq,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro hp,
  split,
  intro a,
  have hpq: P a ∧ Q a,
  exact hp a,
  cases hpq,
  exact hpq_left,
  intro a,
  have hpq: P a ∧ Q a,
  exact hp a,
  cases hpq,
  exact hpq_right,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro hp,
  cases hp with hpp hpq,
  intro a,
  split,
  exact hpp a,
  exact hpq a,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro hp,
  intro hpq,
  cases hp,
  have hq: P hpq := hp hpq,
  left,
  exact hp hpq,
  have hq: Q hpq := hp hpq,
  right,
  exact hp hpq,    
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
