
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro np,
  exact np p,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro nnp,
  by_contradiction p, --RAA
  exact nnp p,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  exact doubleneg_elim P,
  exact doubleneg_intro P,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro pq,
  cases pq with p q,
  right,
  exact p,

  left,
  exact q,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro pq,
  cases pq with p q,
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
  intro npq,
  intro p,
  cases npq with np q,
  exfalso,
  exact np p,

  exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro pq,
  intro np,
  cases pq with p q,
  exfalso,
  exact np p,

  exact q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro pq,
  intro nq,
  intro p,
  exact nq (pq p),
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro nqnp,
  intro p,
  by_contradiction q, --RAA
  exact (nqnp q) p,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  exact impl_as_contrapositive P Q,
  exact impl_as_contrapositive_converse P Q,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro nnpnp,
  apply nnpnp,
  right,
  intro p,
  apply nnpnp,
  left,
  exact p,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro pqp,
  intro np,
  apply np,
  apply pqp,
  intro p,
  exfalso,
  exact np p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro poq,
  intro npenq,
  cases npenq with np nq,
  cases poq with p q,
  exact np p,

  exact nq q,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro peq,
  intro nponq,
  cases peq with p q,
  cases nponq with np nq,
  exact np p,

  exact nq q,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro npeq,
  split,
  intro p,
  apply npeq,
  left,
  exact p,

  intro q,
  apply npeq,
  right,
  exact q,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro npenq,
  intro poq,
  cases npenq with np nq,
  cases poq with p q,
  exact np p,

  exact nq q,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro npeq,
  by_cases p : P, -- LEM
  left,
  intro q,
  apply npeq,
  split,
  exact p,

  exact q,

  right,
  exact p,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro nqonp,
  intro peq,
  cases peq with p q,
  cases nqonp with nq np,
  exact nq q,

  exact np p,
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
  exact demorgan_disj P Q,
  exact demorgan_disj_converse P Q,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro peqor,
  cases peqor with p qor,
  cases qor with q r,
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
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro peqoper,
  cases peqoper with peq per,
  cases peq with p q,
  split,
  exact p,
  left,
  exact q,

  cases per with p r,
  split,
  exact p,
  right,
  exact r,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro poqer,
  split,
  cases poqer with p qer,
  left,
  exact p,

  cases qer with q r,
  right,
  exact q,

  cases poqer with p qer,
  left,
  exact p,

  cases qer with q r,
  right,
  exact r,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro poqepor,
  cases poqepor with poq por,
  cases poq with p q,

  cases por with p r,
  left,
  exact p,

  left,
  exact p,

  cases por with p r,
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
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro peqir,
  intro p,
  intro q,
  apply peqir,
  split,
  exact p,
  exact q,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro piqir,
  intro peq,
  cases peq with p q,
  apply piqir,
  exact p,
  exact q,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro peq,
  cases peq with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro peq,
  cases peq with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  exact weaken_conj_left P P,

  intro p,
  split,
  exact p,
  exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro pop,
  cases pop with p p,
  exact p,
  exact p,

  exact weaken_disj_left P P,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

-- A PARTIR DAQUI FICOU UM POUCO MAIS DIFÍCIL NOMEAR AS COISAS
-- PEÇO PERDÃO DESDE JÁ

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro nexpx,
  intro x,
  intro px,
  apply nexpx,
  existsi x,
  exact px,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro h,
  intro i,
  cases i with i hi,
  have j := h i,
  exact j hi,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro h,
  intro p,
  cases h with h hi,
  have c := p h,
  exact hi c,
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
  intro p,
  cases h with h hi,
  have c := p h,
  exact c hi,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro h,
  intro p,
  cases p with p pi,
  have hp := h p,
  exact pi hp,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro h,
  intro x,
  rw demorgan_exists_law at h,
  have nnx := h x,
  rw doubleneg_law at nnx, -- RAA
  exact nnx,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro h,
  rw demorgan_forall_law at h,
  cases h with i hi,
  existsi i,
  rw doubleneg_law at hi, -- RAA
  exact hi,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  exact forall_as_neg_exists U P,
  exact forall_as_neg_exists_converse U P,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  exact exists_as_neg_forall U P,
  exact exists_as_neg_forall_converse U P,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro p,
  split,
  cases p with i pi,
  cases pi with pi qi,
  existsi i,
  exact pi,

  cases p with i pi,
  cases pi with pi qi,
  existsi i,
  exact qi,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro p,
  cases p with i pi,
  cases pi with pi qi,
  left,
  existsi i,
  exact pi,

  right,
  existsi i,
  exact qi,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro p,
  cases p with p q,
  cases p with i pi,
  existsi i,
  left,
  exact pi,

  cases q with i qi,
  existsi i,
  right,
  exact qi,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro p,
  split,
  intro x,
  have px := p x,
  cases px with px qx,
  exact px,

  intro x,
  have px := p x,
  cases px with px qx,
  exact qx,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro p,
  intro x,
  split,
  cases p with p q,
  have px := p x,
  exact px,

  cases p with p q,
  have qx := q x,
  exact qx,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro p,
  intro x,
  cases p with p q,
  have px := p x,
  left,
  exact px,

  have qx := q x,
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
