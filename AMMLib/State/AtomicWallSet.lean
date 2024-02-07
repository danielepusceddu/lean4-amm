import AMMLib.State.AtomicWall
open NNReal

structure S₀ where
  map: A →₀ W₀

def S₀.get (s: S₀) (a: A): W₀ :=
  s.map a

@[ext]
theorem S₀.ext {s1 s2: S₀} (h: ∀ a, s1.get a = s2.get a): s1 = s2 := by
    unfold get at h
    rcases s1 with ⟨f⟩
    rcases s2 with ⟨f'⟩
    simp only [mk.injEq]
    simp at h
    ext a: 1
    exact h a

@[simp] theorem S₀.map_eq_get (s: S₀): s.map = s.get := by ext; simp [get]

noncomputable def S₀.add (s: S₀) (a: A) (t: T) (x: ℝ≥0): S₀ :=
  ⟨s.map.update a ((s.map a).add t x)⟩

@[simp] theorem S₀.get_add_self (s: S₀) (a: A) (t: T) (x: ℝ≥0):
  (s.add a t x).get a = (s.get a).add t x := by
  simp [get, add]

@[simp] theorem S₀.get_add_diffa (s: S₀) (a: A) (t: T) (x: ℝ≥0)
  (a': A) (hdif: a ≠ a'):
  (s.add a t x).get a' = s.get a' := by
  simp [get, add, hdif.symm]

noncomputable def S₀.sub (s: S₀) (a: A) (t: T) (x: ℝ≥0) (h: x ≤ s.get a t): S₀ :=
  ⟨s.map.update a ((s.map a).sub t x h)⟩

@[simp] theorem S₀.get_sub_self (s: S₀) (a: A) (t: T) (x: ℝ≥0) (h: x ≤ s.get a t):
  (s.sub a t x h).get a = (s.get a).sub t x h := by
  simp [get, sub]

@[simp] theorem S₀.get_sub_diffa (s: S₀) (a: A) (t: T) (x: ℝ≥0) (h: x ≤ s.get a t) (a': A) (hdif: a ≠ a'):
  (s.sub a t x h).get a' = s.get a' := by
  simp [get, sub, hdif.symm]

noncomputable def S₀.drainw (s: S₀) (a: A): S₀ :=
  ⟨Finsupp.erase a s.map⟩

theorem S₀.supply (s: S₀) (t: T): ℝ≥0 :=
  s.map.sum (λ _ w => w t)

-- When adding balance to a wallet,
-- we are adding to the set's supply of that token as well.
@[simp] theorem S₀.supply_of_add_self (s: S₀) (a: A)
  (t: T) (x: ℝ≥0):
  (s.add a t x).supply t = s.supply t + x := by
  unfold supply
  rw [← Finsupp.add_sum_erase' (s.map) a _ (by simp)]
  rw [← Finsupp.add_sum_erase' _ a _ (by simp)]

  have h:
    Finsupp.erase a (s.add a t x).map = Finsupp.erase a s.map := by
    ext a' t'
    rcases Decidable.em (a'=a) with uh|uh
    . simp [uh]
    . simp [Ne.intro uh, (Ne.intro uh).symm]

  rw [add_assoc, add_comm _ x, ← add_assoc]
  simp [h]

-- Supplies of other tokens remain unchanged.
@[simp] theorem S₀.supply_of_add_diff (s: S₀) (a: A) (t: T)
  (x: ℝ≥0) (t': T) (hdiff: t ≠ t'):
  (s.add a t x).supply t' = s.supply t' := by
  unfold supply
  rw [← Finsupp.add_sum_erase' _ a _ (by simp)]
  rw [← Finsupp.add_sum_erase' s.map a _ (by simp)]

  have h:
    Finsupp.erase a (s.add a t x).map = Finsupp.erase a s.map := by
    ext a' t'
    rcases Decidable.em (a'=a) with uh|uh
    . simp [uh]
    . simp [Ne.intro uh, (Ne.intro uh).symm]

  simp [h, hdiff]

@[simp] theorem S₀.supply_of_sub_self (s: S₀) (a: A) (t: T) (x: ℝ≥0) (h: x ≤ s.get a t):
  (s.sub a t x h).supply t = s.supply t - x := by
  unfold supply
  rw [← Finsupp.add_sum_erase' (s.map) a _ (by simp)]
  rw [← Finsupp.add_sum_erase' _ a _ (by simp)]

  have h': Finsupp.erase a (s.sub a t x h).map = Finsupp.erase a s.map := by
    ext a' t'
    rcases Decidable.em (a'=a) with uh|uh
    . simp [uh]
    . simp [Ne.intro uh, (Ne.intro uh).symm]

  rw [h']
  rw [map_eq_get, map_eq_get]
  rw [← tsub_add_eq_add_tsub h]
  simp

@[simp] theorem S₀.supply_of_sub_diff (s: S₀) (a: A) (t: T) (x: ℝ≥0) (h: x ≤ s.get a t) (t': T) (hdifp: t ≠ t'):
  (s.sub a t x h).supply t' = s.supply t' := by
  unfold supply
  rw [← Finsupp.add_sum_erase' (s.map) a _ (by simp)]
  rw [← Finsupp.add_sum_erase' _ a _ (by simp)]

  have h': Finsupp.erase a (s.sub a t x h).map = Finsupp.erase a s.map := by
    ext a' t'
    rcases Decidable.em (a'=a) with uh|uh
    . simp [uh]
    . simp [Ne.intro uh, (Ne.intro uh).symm]

  simp [h', hdifp]
