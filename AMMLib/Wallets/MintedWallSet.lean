import AMMLib.Wallets.MintedWall

structure 𝕊₁ where
  f: 𝔸 →₀ 𝕎₁

def 𝕊₁.empty: 𝕊₁ := ⟨0⟩

def 𝕊₁.get (s: 𝕊₁) (a: 𝔸): 𝕎₁ :=
  s.f a

@[simp] theorem 𝕊₁.f_eq_get (s: 𝕊₁):
  s.f = s.get := by rfl

noncomputable def 𝕊₁.add (s: 𝕊₁) (a: 𝔸) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1) (x: NNReal): 𝕊₁ :=
  ⟨s.f.update a ((s.f a).add t0 t1 hdif x)⟩

@[simp] theorem 𝕊₁.get_add_self (s: 𝕊₁) (a: 𝔸) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1) (x: NNReal):
  (s.add a t0 t1 hdif x).get a = (s.get a).add t0 t1 hdif x := by
  simp [get, add]

@[simp] theorem 𝕊₁.get_add_diff (s: 𝕊₁) (a: 𝔸) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1) (x: NNReal) (a': 𝔸) (hdiff: a ≠ a'):
  (s.add a t0 t1 hdif x).get a' = s.get a' := by
  simp [get, add, hdiff.symm]

noncomputable def 𝕊₁.sub (s: 𝕊₁) (a: 𝔸) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1) (x: NNReal) (h: x ≤ (s.get a).f t0 t1): 𝕊₁ :=
  ⟨s.f.update a ((s.f a).sub t0 t1 hdif x h)⟩

@[simp] theorem 𝕊₁.get_sub_self (s: 𝕊₁) (a: 𝔸) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1) (x: NNReal) (h: x ≤ (s.get a).f t0 t1):
  (s.sub a t0 t1 hdif x h).get a = (s.get a).sub t0 t1 hdif x h := by
  simp [get, sub]

@[simp] theorem 𝕊₁.get_sub_diff (s: 𝕊₁) (a: 𝔸) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1) (x: NNReal) (h: x ≤ (s.get a).f t0 t1) (a': 𝔸) (hdiff: a ≠ a'):
  (s.sub a t0 t1 hdif x h).get a' = s.get a' := by
  simp [get, sub, hdiff.symm]

noncomputable def 𝕊₁.drain (s: 𝕊₁) (a: 𝔸) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1): 𝕊₁ := 
  ⟨s.f.update a ((s.f a).drain t0 t1 hdif)⟩

@[simp] theorem 𝕊₁.get_drain_self (w: 𝕊₁) (a: 𝔸) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1):
  (w.drain a t0 t1 hdif).get a = (w.get a).drain t0 t1 hdif := by
  unfold drain
  unfold get
  simp

@[simp] theorem 𝕊₁.get_drain_diff (w: 𝕊₁) (a: 𝔸) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1) (a': 𝔸) (hdiff: a ≠ a'):
  (w.drain a t0 t1 hdif).get a' = w.get a' := by
  unfold drain
  unfold get
  simp [hdiff.symm]

theorem 𝕊₁.supply (s: 𝕊₁) (t0 t1: 𝕋₀): NNReal :=
  s.f.sum (λ _ w => w.get t0 t1)

theorem 𝕊₁.supply_reorder (s: 𝕊₁) (t1 t0: 𝕋₀): 
  s.supply t1 t0 = s.supply t0 t1 := by
  unfold supply
  simp_rw [𝕎₁.get_reorder]

@[simp] theorem 𝕊₁.supply_of_add_self (s: 𝕊₁) (a: 𝔸) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1) (x: NNReal): 
  (s.add a t0 t1 hdif x).supply t0 t1 = s.supply t0 t1 + x := by
  unfold supply
  rw [← Finsupp.add_sum_erase' _ a _ (by simp)]
  rw [← Finsupp.add_sum_erase' s.f a _ (by simp)]

  have h: Finsupp.erase a (s.add a t0 t1 hdif x).f = Finsupp.erase a s.f := 
  by ext a'
     rcases Decidable.em (a'=a) with eq|neq
     . simp [eq]
     . rw [Finsupp.erase_ne (Ne.intro neq)]
       rw [Finsupp.erase_ne (Ne.intro neq)]
       simp [(Ne.intro neq).symm]

  rw [h]
  conv => rhs; rw [add_assoc, add_comm _ x, ← add_assoc]; rfl
  simp

@[simp] theorem 𝕊₁.supply_of_add_diff (s: 𝕊₁) (a: 𝔸) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1) (x: NNReal) (t0' t1': 𝕋₀) (hdiffp: diffpair t0 t1 t0' t1'): 
  (s.add a t0 t1 hdif x).supply t0' t1' = s.supply t0' t1' := by
  unfold supply
  rw [← Finsupp.add_sum_erase' _ a _ (by simp)]
  rw [← Finsupp.add_sum_erase' s.f a _ (by simp)]

  have h: Finsupp.erase a (s.add a t0 t1 hdif x).f = Finsupp.erase a s.f := 
  by ext a'
     rcases Decidable.em (a'=a) with eq|neq
     . simp [eq]
     . rw [Finsupp.erase_ne (Ne.intro neq)]
       rw [Finsupp.erase_ne (Ne.intro neq)]
       simp [(Ne.intro neq).symm]

  rw [h]
  simp [hdiffp]

@[simp] theorem 𝕊₁.supply_of_sub_self (s: 𝕊₁) (a: 𝔸) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1) (x: NNReal) (h: x ≤ (s.get a).get t0 t1): 
  (s.sub a t0 t1 hdif x h).supply t0 t1 = s.supply t0 t1 - x := by
  unfold supply
  rw [← Finsupp.add_sum_erase' _ a _ (by simp)]
  rw [← Finsupp.add_sum_erase' s.f a _ (by simp)]

  have h': Finsupp.erase a (s.sub a t0 t1 hdif x h).f = Finsupp.erase a s.f := 
  by ext a'
     rcases Decidable.em (a'=a) with eq|neq
     . simp [eq]
     . rw [Finsupp.erase_ne (Ne.intro neq)]
       rw [Finsupp.erase_ne (Ne.intro neq)]
       simp [(Ne.intro neq).symm]

  rw [h', f_eq_get, f_eq_get]
  conv => rhs; rw [← tsub_add_eq_add_tsub h]
  simp

@[simp] theorem 𝕊₁.supply_of_sub_diff (s: 𝕊₁) (a: 𝔸) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1) (x: NNReal) (h: x ≤ (s.get a).f t0 t1) (t0' t1': 𝕋₀) (hdiffp: diffpair t0 t1 t0' t1'): 
  (s.sub a t0 t1 hdif x h).supply t0' t1' = s.supply t0' t1' := by

  unfold supply
  rw [← Finsupp.add_sum_erase' _ a _ (by simp)]
  rw [← Finsupp.add_sum_erase' s.f a _ (by simp)]

  have h': Finsupp.erase a (s.sub a t0 t1 hdif x h).f = Finsupp.erase a s.f := 
  by ext a'
     rcases Decidable.em (a'=a) with eq|neq
     . simp [eq]
     . rw [Finsupp.erase_ne (Ne.intro neq)]
       rw [Finsupp.erase_ne (Ne.intro neq)]
       simp [(Ne.intro neq).symm]

  rw [h']
  simp [hdiffp]