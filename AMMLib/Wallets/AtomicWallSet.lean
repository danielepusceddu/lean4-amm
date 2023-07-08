import AMMLib.Wallets.AtomicWall

structure 𝕊₀ where
  f: 𝔸 →₀ 𝕎₀

def 𝕊₀.get (s: 𝕊₀) (a: 𝔸): 𝕎₀ :=
  s.f a

theorem 𝕊₀.eq_iff (s s': 𝕊₀):
  s = s' ↔ ∀ (a: 𝔸), s.get a = s'.get a := by
  apply Iff.intro
  . intro seq a
    rw [seq]
  . intro feq
    unfold get at feq
    rcases s with ⟨f⟩
    rcases s' with ⟨f'⟩
    simp only [mk.injEq]
    simp at feq
    ext a: 1
    exact feq a

@[simp] theorem 𝕊₀.f_eq_get (s: 𝕊₀): s.f = s.get := by simp [get]

noncomputable def 𝕊₀.add (s: 𝕊₀) (a: 𝔸) (t: 𝕋) (x: NNReal): 𝕊₀ :=
  ⟨s.f.update a ((s.f a).add t x)⟩

@[simp] theorem 𝕊₀.get_add_self (s: 𝕊₀) (a: 𝔸) (t: 𝕋) (x: NNReal):
  (s.add a t x).get a = (s.get a).add t x := by
  simp [get, add]

@[simp] theorem 𝕊₀.get_add_diffa (s: 𝕊₀) (a: 𝔸) (t: 𝕋) (x: NNReal) (a': 𝔸) (hdif: a ≠ a'):
  (s.add a t x).get a' = s.get a' := by
  simp [get, add, hdif.symm]

noncomputable def 𝕊₀.sub (s: 𝕊₀) (a: 𝔸) (t: 𝕋) (x: NNReal) (h: x ≤ s.get a t): 𝕊₀ :=
  ⟨s.f.update a ((s.f a).sub t x h)⟩

@[simp] theorem 𝕊₀.get_sub_self (s: 𝕊₀) (a: 𝔸) (t: 𝕋) (x: NNReal) (h: x ≤ s.get a t):
  (s.sub a t x h).get a = (s.get a).sub t x h := by 
  simp [get, sub]

@[simp] theorem 𝕊₀.get_sub_diffa (s: 𝕊₀) (a: 𝔸) (t: 𝕋) (x: NNReal) (h: x ≤ s.get a t) (a': 𝔸) (hdif: a ≠ a'):
  (s.sub a t x h).get a' = s.get a' := by
  simp [get, sub, hdif.symm]

noncomputable def 𝕊₀.drainw (s: 𝕊₀) (a: 𝔸): 𝕊₀ :=
  ⟨Finsupp.erase a s.f⟩

theorem 𝕊₀.supply (s: 𝕊₀) (t: 𝕋): NNReal :=
  s.f.sum (λ _ w => w t)

@[simp] theorem 𝕊₀.supply_of_add_self (s: 𝕊₀) (a: 𝔸) (t: 𝕋) (x: NNReal): 
  (s.add a t x).supply t = s.supply t + x := by
  unfold supply
  rw [← Finsupp.add_sum_erase' (s.f) a _ (by simp)]
  rw [← Finsupp.add_sum_erase' _ a _ (by simp)]

  have h: Finsupp.erase a (s.add a t x).f = Finsupp.erase a s.f := by
    ext a' t'
    rcases Decidable.em (a'=a) with uh|uh
    . simp [uh]
    . simp [Ne.intro uh, (Ne.intro uh).symm]

  rw [add_assoc, add_comm _ x, ← add_assoc]
  simp [h]

@[simp] theorem 𝕊₀.supply_of_add_diff (s: 𝕊₀) (a: 𝔸) (t: 𝕋) (x: NNReal) (t': 𝕋) (hdiff: t ≠ t'): 
  (s.add a t x).supply t' = s.supply t' := by
  unfold supply
  rw [← Finsupp.add_sum_erase' _ a _ (by simp)]
  rw [← Finsupp.add_sum_erase' s.f a _ (by simp)]

  have h: Finsupp.erase a (s.add a t x).f = Finsupp.erase a s.f := by
    ext a' t'
    rcases Decidable.em (a'=a) with uh|uh
    . simp [uh]
    . simp [Ne.intro uh, (Ne.intro uh).symm]
  
  simp [h, hdiff]

@[simp] theorem 𝕊₀.supply_of_sub_self (s: 𝕊₀) (a: 𝔸) (t: 𝕋) (x: NNReal) (h: x ≤ s.get a t): 
  (s.sub a t x h).supply t = s.supply t - x := by
  unfold supply
  rw [← Finsupp.add_sum_erase' (s.f) a _ (by simp)]
  rw [← Finsupp.add_sum_erase' _ a _ (by simp)]

  have h': Finsupp.erase a (s.sub a t x h).f = Finsupp.erase a s.f := by
    ext a' t'
    rcases Decidable.em (a'=a) with uh|uh
    . simp [uh]
    . simp [Ne.intro uh, (Ne.intro uh).symm]

  rw [h']
  rw [f_eq_get, f_eq_get]
  rw [← tsub_add_eq_add_tsub h]
  simp

@[simp] theorem 𝕊₀.supply_of_sub_diff (s: 𝕊₀) (a: 𝔸) (t: 𝕋) (x: NNReal) (h: x ≤ s.get a t) (t': 𝕋) (hdifp: t ≠ t'): 
  (s.sub a t x h).supply t' = s.supply t' := by
  unfold supply
  rw [← Finsupp.add_sum_erase' (s.f) a _ (by simp)]
  rw [← Finsupp.add_sum_erase' _ a _ (by simp)]

  have h': Finsupp.erase a (s.sub a t x h).f = Finsupp.erase a s.f := by
    ext a' t'
    rcases Decidable.em (a'=a) with uh|uh
    . simp [uh]
    . simp [Ne.intro uh, (Ne.intro uh).symm]

  simp [h', hdifp]