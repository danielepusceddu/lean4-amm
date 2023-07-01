import AMMLib.Wallets.AtomicWall

structure 𝕊₀ where
  f: 𝔸 →₀ 𝕎₀

def 𝕊₀.get (s: 𝕊₀) (a: 𝔸): 𝕎₀ :=
  s.f a

noncomputable def 𝕊₀.add (s: 𝕊₀) (a: 𝔸) (t: 𝕋₀) (x: NNReal): 𝕊₀ :=
  ⟨s.f.update a ((s.f a).add t x)⟩

@[simp] theorem 𝕊₀.get_add_self (s: 𝕊₀) (a: 𝔸) (t: 𝕋₀) (x: NNReal):
  (s.add a t x).get a = (s.get a).add t x := by sorry

@[simp] theorem 𝕊₀.get_add_diffa (s: 𝕊₀) (a: 𝔸) (t: 𝕋₀) (x: NNReal) (a': 𝔸) (hdif: a ≠ a'):
  (s.add a t x).get a' = s.get a' := by sorry

noncomputable def 𝕊₀.sub (s: 𝕊₀) (a: 𝔸) (t: 𝕋₀) (x: NNReal) (h: x ≤ s.get a t): 𝕊₀ :=
  ⟨s.f.update a ((s.f a).sub t x h)⟩

@[simp] theorem 𝕊₀.get_sub_self (s: 𝕊₀) (a: 𝔸) (t: 𝕋₀) (x: NNReal) (h: x ≤ s.get a t):
  (s.sub a t x h).get a = (s.get a).sub t x h := by sorry

@[simp] theorem 𝕊₀.get_sub_difft (s: 𝕊₀) (a: 𝔸) (t: 𝕋₀) (x: NNReal) (h: x ≤ s.get a t) (a': 𝔸) (hdif: a ≠ a'):
  (s.sub a t x h).get a' = s.get a' := by sorry

theorem 𝕊₀.supply (s: 𝕊₀) (t: 𝕋₀): NNReal :=
  s.f.sum (λ _ w => w t)

@[simp] theorem 𝕊₀.supply_of_add_self (s: 𝕊₀) (a: 𝔸) (t: 𝕋₀) (x: NNReal): 
  (s.add a t x).supply t = s.supply t + x := by sorry

@[simp] theorem 𝕊₀.supply_of_add_diff (s: 𝕊₀) (a: 𝔸) (t: 𝕋₀) (x: NNReal) (t': 𝕋₀) (hdiff: t ≠ t'): 
  (s.add a t x).supply t' = s.supply t' := by sorry

@[simp] theorem 𝕊₀.supply_of_sub_self (s: 𝕊₀) (a: 𝔸) (t: 𝕋₀) (x: NNReal) (h: x ≤ s.get a t): 
  (s.sub a t x h).supply t = s.supply t - x := by sorry

@[simp] theorem 𝕊₀.supply_of_sub_diff (s: 𝕊₀) (a: 𝔸) (t: 𝕋₀) (x: NNReal) (h: x ≤ s.get a t) (t': 𝕋₀) (hdifp: t ≠ t'): 
  (s.sub a t x h).supply t' = s.supply t' := by sorry