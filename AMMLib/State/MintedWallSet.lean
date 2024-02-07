import AMMLib.State.MintedWall
open NNReal

-- Set of minted token wallets
structure S₁ where
  map: A →₀ W₁

def S₁.empty: S₁ := ⟨0⟩

def S₁.get (s: S₁) (a: A): W₁ :=
  s.map a

@[simp] theorem S₁.map_eq_get (s: S₁):
  s.map = s.get := by rfl

noncomputable def S₁.add (s: S₁) (a: A) (t0 t1: T) (hdif: t0 ≠ t1) (x: ℝ≥0): S₁ :=
  ⟨s.map.update a ((s.map a).add t0 t1 hdif x)⟩

@[simp] theorem S₁.get_add_self (s: S₁) (a: A) (t0 t1: T) (hdif: t0 ≠ t1) (x: ℝ≥0):
  (s.add a t0 t1 hdif x).get a = (s.get a).add t0 t1 hdif x := by
  simp [get, add]

@[simp] theorem S₁.get_add_diff (s: S₁) (a: A) (t0 t1: T) (hdif: t0 ≠ t1) (x: ℝ≥0) (a': A) (hdiff: a ≠ a'):
  (s.add a t0 t1 hdif x).get a' = s.get a' := by
  simp [get, add, hdiff.symm]

noncomputable def S₁.sub (s: S₁) (a: A) (t0 t1: T) (hdif: t0 ≠ t1) (x: ℝ≥0) (h: x ≤ (s.get a).bal t0 t1): S₁ :=
  ⟨s.map.update a ((s.map a).sub t0 t1 hdif x h)⟩

@[simp] theorem S₁.get_sub_self (s: S₁) (a: A) (t0 t1: T) (hdif: t0 ≠ t1) (x: ℝ≥0) (h: x ≤ (s.get a).bal t0 t1):
  (s.sub a t0 t1 hdif x h).get a = (s.get a).sub t0 t1 hdif x h := by
  simp [get, sub]

@[simp] theorem S₁.get_sub_diff (s: S₁) (a: A) (t0 t1: T) (hdif: t0 ≠ t1) (x: ℝ≥0) (h: x ≤ (s.get a).bal t0 t1) (a': A) (hdiff: a ≠ a'):
  (s.sub a t0 t1 hdif x h).get a' = s.get a' := by
  simp [get, sub, hdiff.symm]

noncomputable def S₁.drain (s: S₁) (a: A) (t0 t1: T) (hdif: t0 ≠ t1): S₁ :=
  ⟨s.map.update a ((s.map a).drain t0 t1 hdif)⟩

@[simp] theorem S₁.get_drain_self (w: S₁) (a: A) (t0 t1: T) (hdif: t0 ≠ t1):
  (w.drain a t0 t1 hdif).get a = (w.get a).drain t0 t1 hdif := by
  unfold drain
  unfold get
  simp

@[simp] theorem S₁.get_drain_diff (w: S₁) (a: A) (t0 t1: T) (hdif: t0 ≠ t1) (a': A) (hdiff: a ≠ a'):
  (w.drain a t0 t1 hdif).get a' = w.get a' := by
  unfold drain
  unfold get
  simp [hdiff.symm]

theorem S₁.supply (s: S₁) (t0 t1: T): ℝ≥0 :=
  s.map.sum (λ _ w => w.get t0 t1)

@[simp] theorem S₁.supply_of_empty (t0 t1: T): empty.supply t0 t1 = 0 := by
  unfold supply
  unfold empty
  simp

theorem S₁.supply_reorder (s: S₁) (t1 t0: T):
  s.supply t1 t0 = s.supply t0 t1 := by
  unfold supply
  simp_rw [W₁.get_reorder]

theorem S₁.supply_samepair (s: S₁) (t0 t1 t0' t1': T) (samepair: samemint t0 t1 t0' t1'):
  s.supply t0 t1 = s.supply t0' t1' := by
  unfold samemint at samepair
  rcases samepair with ⟨l,r⟩|⟨l,r⟩
  . rw [l, r]
  . rw [l, r]
    exact supply_reorder _ _ _

theorem S₁.supply_destroy (s: S₁) (a: A) (t0 t1: T) (hdif: t0 ≠ t1):
  s.supply t0 t1 = (s.drain a t0 t1 hdif).supply t0 t1 + (s.get a).get t0 t1 := by

  have h: Finsupp.erase a (drain s a t0 t1 hdif).map = Finsupp.erase a s.map
  := by ext a'
        rcases Decidable.em (a' = a) with eq|neq
        . simp [eq]
        . simp [neq, (Ne.intro neq).symm]

  unfold supply
  rw [← Finsupp.add_sum_erase' _ a _ (by simp)]
  rw [Finsupp.sum_zero' (drain s a t0 t1 hdif).map _ a (by simp)]
  rw [add_comm]
  rw [h, get]

theorem S₁.get_pos_imp_supp_pos
  (w: S₁) (t0 t1: T) (a: A) (h: 0 < (w.get a).get t0 t1):
  0 < w.supply t0 t1 := by

  have hdif: t0 ≠ t1 := by
    by_contra contra
    rw [contra] at h
    have h' := (w.get a).distinct t1
    unfold W₁.get at h
    have h'' := (ne_of_lt h).symm
    contradiction

  rw [w.supply_destroy a t0 t1 hdif]
  rw [add_comm]
  have h'' := ne_of_gt h
  exact NNReal.neq_zero_imp_gt ((NNReal.pos_imp_add_pos ((w.get a).get t0 t1) ((w.drain a t0 t1 hdif).supply t0 t1) h''))

@[simp] theorem S₁.supply_of_add_self (s: S₁) (a: A) (t0 t1: T) (hdif: t0 ≠ t1) (x: ℝ≥0):
  (s.add a t0 t1 hdif x).supply t0 t1 = s.supply t0 t1 + x := by
  unfold supply
  rw [← Finsupp.add_sum_erase' _ a _ (by simp)]
  rw [← Finsupp.add_sum_erase' s.map a _ (by simp)]

  have h: Finsupp.erase a (s.add a t0 t1 hdif x).map = Finsupp.erase a s.map :=
  by ext a'
     rcases Decidable.em (a'=a) with eq|neq
     . simp [eq]
     . rw [Finsupp.erase_ne (Ne.intro neq)]
       rw [Finsupp.erase_ne (Ne.intro neq)]
       simp [(Ne.intro neq).symm]

  rw [h]
  conv => rhs; rw [add_assoc, add_comm _ x, ← add_assoc]; rfl
  simp

@[simp] theorem S₁.supply_of_add_diff (s: S₁) (a: A) (t0 t1: T) (hdif: t0 ≠ t1) (x: ℝ≥0) (t0' t1': T) (hdiffp: diffmint t0 t1 t0' t1'):
  (s.add a t0 t1 hdif x).supply t0' t1' = s.supply t0' t1' := by
  unfold supply
  rw [← Finsupp.add_sum_erase' _ a _ (by simp)]
  rw [← Finsupp.add_sum_erase' s.map a _ (by simp)]

  have h: Finsupp.erase a (s.add a t0 t1 hdif x).map = Finsupp.erase a s.map :=
  by ext a'
     rcases Decidable.em (a'=a) with eq|neq
     . simp [eq]
     . rw [Finsupp.erase_ne (Ne.intro neq)]
       rw [Finsupp.erase_ne (Ne.intro neq)]
       simp [(Ne.intro neq).symm]

  rw [h]
  simp [hdiffp]

@[simp] theorem S₁.supply_of_sub_self (s: S₁) (a: A) (t0 t1: T) (hdif: t0 ≠ t1) (x: ℝ≥0) (h: x ≤ (s.get a).get t0 t1):
  (s.sub a t0 t1 hdif x h).supply t0 t1 = s.supply t0 t1 - x := by
  unfold supply
  rw [← Finsupp.add_sum_erase' _ a _ (by simp)]
  rw [← Finsupp.add_sum_erase' s.map a _ (by simp)]

  have h': Finsupp.erase a (s.sub a t0 t1 hdif x h).map = Finsupp.erase a s.map :=
  by ext a'
     rcases Decidable.em (a'=a) with eq|neq
     . simp [eq]
     . rw [Finsupp.erase_ne (Ne.intro neq)]
       rw [Finsupp.erase_ne (Ne.intro neq)]
       simp [(Ne.intro neq).symm]

  rw [h', map_eq_get, map_eq_get]
  conv => rhs; rw [← tsub_add_eq_add_tsub h]
  simp

@[simp] theorem S₁.supply_of_sub_diff (s: S₁) (a: A) (t0 t1: T) (hdif: t0 ≠ t1) (x: ℝ≥0) (h: x ≤ (s.get a).bal t0 t1) (t0' t1': T) (hdiffp: diffmint t0 t1 t0' t1'):
  (s.sub a t0 t1 hdif x h).supply t0' t1' = s.supply t0' t1' := by

  unfold supply
  rw [← Finsupp.add_sum_erase' _ a _ (by simp)]
  rw [← Finsupp.add_sum_erase' s.map a _ (by simp)]

  have h': Finsupp.erase a (s.sub a t0 t1 hdif x h).map = Finsupp.erase a s.map :=
  by ext a'
     rcases Decidable.em (a'=a) with eq|neq
     . simp [eq]
     . rw [Finsupp.erase_ne (Ne.intro neq)]
       rw [Finsupp.erase_ne (Ne.intro neq)]
       simp [(Ne.intro neq).symm]

  rw [h']
  simp [hdiffp]
