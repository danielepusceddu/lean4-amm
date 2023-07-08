import AMMLib.AMMSet

def 𝕊ₐ.r0₀ (amms: 𝕊ₐ) (t0 t1: 𝕋): NNReal := amms.f t0 t1

def 𝕊ₐ.r1₀ (amms: 𝕊ₐ) (t0 t1: 𝕋): NNReal := amms.f t1 t0

@[simp] theorem 𝕊ₐ.r0_same₀ (amms: 𝕊ₐ) (t: 𝕋):
  amms.r0₀ t t = 0 := by simp [r0₀, amms.h2]

@[simp] theorem 𝕊ₐ.r1_same₀ (amms: 𝕊ₐ) (t: 𝕋):
  amms.r1₀ t t = 0 := by simp [r1₀, amms.h2]

@[simp] theorem 𝕊ₐ.r0_toNNReal (amms: 𝕊ₐ) (t0 t1: 𝕋) (hinit: amms.init t0 t1):
  amms.r0 t0 t1 hinit = amms.r0₀ t0 t1 := by simp [r0, r0₀]

@[simp] theorem 𝕊ₐ.r1_toNNReal (amms: 𝕊ₐ) (t0 t1: 𝕋) (hinit: amms.init t0 t1):
  amms.r1 t0 t1 hinit = amms.r1₀ t0 t1 := by simp [r1, r1₀]

theorem 𝕊ₐ.r0_reorder₀
  (amms: 𝕊ₐ) (t1 t0: 𝕋):
  amms.r0₀ t1 t0 = amms.r1₀ t0 t1 := by
  simp [r0₀, r1₀]

theorem 𝕊ₐ.r1_reorder₀
  (amms: 𝕊ₐ) (t1 t0: 𝕋):
  amms.r1₀ t1 t0 = amms.r0₀ t0 t1 := by
  simp [r0₀, r1₀]

@[simp] theorem 𝕊ₐ.r0_of_initialize₀
  (amms: 𝕊ₐ) {t0 t1: 𝕋} (hdif: t0 ≠ t1) (r0 r1: ℝ+):
  (amms.initialize hdif r0 r1).r0₀ t0 t1 = r0 := by 
  simp [𝕊ₐ.r0₀, 𝕊ₐ.initialize, hdif]

@[simp] theorem 𝕊ₐ.r1_of_initialize₀
  (amms: 𝕊ₐ) {t0 t1: 𝕋} (hdif: t0 ≠ t1) (r0 r1: ℝ+):
  (amms.initialize hdif r0 r1).r1₀ t0 t1 = r1 := by 
  simp [𝕊ₐ.r1₀, 𝕊ₐ.initialize, hdif]

@[simp] theorem 𝕊ₐ.r0_of_initialize_diffpair₀
  (amms: 𝕊ₐ) {t0 t1: 𝕋} (hdif: t0 ≠ t1) (r0 r1: ℝ+)
  (t0' t1': 𝕋) (difp: diffmint t0 t1 t0' t1'):
  (amms.initialize hdif r0 r1).r0₀ t0' t1' = amms.r0₀ t0' t1' := by 

  rcases Decidable.em (t0'=t1') with eq|dif'
  . simp [eq]
  . have hdif' := Ne.intro dif'
    rcases difp with ⟨a,b⟩|⟨a,b⟩
    . rcases Decidable.em (t1=t1') with c|c
      . simp [𝕊ₐ.r0₀, 𝕊ₐ.initialize, a.symm, c, hdif']
      . rcases Decidable.em (t0'=t1) with d|d
        . simp [𝕊ₐ.r0₀, 𝕊ₐ.initialize, a.symm, b.symm, c, hdif', d]
        . simp [𝕊ₐ.r0₀, 𝕊ₐ.initialize, a.symm, c, hdif', d]
    . rcases Decidable.em (t0=t1') with c|c
      . simp [𝕊ₐ.r0₀, 𝕊ₐ.initialize, a.symm, c, hdif']
      . rcases Decidable.em (t0'=t0) with d|d
        . simp [𝕊ₐ.r0₀, 𝕊ₐ.initialize, b.symm, d, hdif]
        . simp [𝕊ₐ.r0₀, 𝕊ₐ.initialize, a.symm, c, hdif', d]

@[simp] theorem 𝕊ₐ.r1_of_initialize_diffpair₀
  (amms: 𝕊ₐ) {t0 t1: 𝕋} (hdif: t0 ≠ t1) (r0 r1: ℝ+)
  (t0' t1': 𝕋) (difp: diffmint t0 t1 t0' t1'):
  (amms.initialize hdif r0 r1).r1₀ t0' t1' = amms.r1₀ t0' t1' := by 
  rw [r1_reorder₀ _ t0' t1']
  rw [r1_reorder₀ amms t0' t1']
  simp [(diffmint.iff_swap_inner_right t0 t1 t0' t1').mp difp]

@[simp] theorem 𝕊ₐ.r0_of_add_r0₀
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (x: PReal)
  (h: amms.init t0 t1)
  :
  (amms.add_r0 t0 t1 h x).r0₀ t0 t1
  =
  x + amms.r0₀ t0 t1
  := by rw [add_comm]; simp [add_r0]

@[simp] theorem 𝕊ₐ.r0_of_add_r0_diff₀
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (x: PReal)
  (h: amms.init t0 t1) (t0' t1': 𝕋)
  (hdiff: diffmint t0 t1 t0' t1'):
  (amms.add_r0 t0 t1 h x).r0₀ t0' t1'
  =
  amms.r0₀ t0' t1'
  := by simp [add_r0, hdiff]

@[simp] theorem 𝕊ₐ.r0_of_add_r1₀
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: PReal):
  (amms.add_r1 t0 t1 h x).r0₀ t0 t1
  =
  amms.r0₀ t0 t1
  := by simp [add_r1]

@[simp] theorem 𝕊ₐ.r0_of_add_r1_diff₀
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (x: PReal)
  (h: amms.init t0 t1) 
  (t0' t1': 𝕋)
  (hdiff: diffmint t0 t1 t0' t1')
  :
  (amms.add_r1 t0 t1 h x).r0₀ t0' t1'
  =
  amms.r0₀ t0' t1'
  := by 
  simp [add_r1, hdiff]

@[simp] theorem 𝕊ₐ.r1_of_add_r1₀
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: ℝ+):
  (amms.add_r1 t0 t1 h x).r1₀ t0 t1
  =
  x + amms.r1₀ t0 t1
  := by rw [add_comm]; simp [add_r1]

@[simp] theorem 𝕊ₐ.r1_of_add_r1_diff₀
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (x: PReal)
  (h: amms.init t0 t1) (t0' t1': 𝕋)
  (hdiff: diffmint t0 t1 t0' t1'):
  (amms.add_r1 t0 t1 h x).r1₀ t0' t1'
  =
  amms.r1₀ t0' t1'
  := by simp [add_r1, hdiff]

@[simp] theorem 𝕊ₐ.r1_of_add_r0₀
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: ℝ+):
  (amms.add_r0 t0 t1 h x).r1₀ t0 t1
  =
  amms.r1₀ t0 t1
  := by simp [add_r0]

@[simp] theorem 𝕊ₐ.r1_of_add_r0_diff₀
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (x: PReal)
  (h: amms.init t0 t1) 
  (t0' t1': 𝕋)(hdiff: diffmint t0 t1 t0' t1'):
  (amms.add_r0 t0 t1 h x).r1₀ t0' t1'
  =
  amms.r1₀ t0' t1'
  := by simp [add_r0, hdiff]

@[simp] theorem 𝕊ₐ.r0_of_sub_r0₀
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r0 t0 t1 h):
  (amms.sub_r0 t0 t1 h x h').r0₀ t0 t1
  =
  amms.r0₀ t0 t1 - x
  := by simp [sub_r0]

@[simp] theorem 𝕊ₐ.r0_of_sub_r1₀
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r1 t0 t1 h):
  (amms.sub_r1 t0 t1 h x h').r0₀ t0 t1
  =
  amms.r0₀ t0 t1
  := by simp [sub_r1]

@[simp] theorem 𝕊ₐ.r1_of_sub_r1₀
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r1 t0 t1 h):
  (amms.sub_r1 t0 t1 h x h').r1₀ t0 t1
  =
  amms.r1₀ t0 t1 - x
  := by simp [sub_r1]

@[simp] theorem 𝕊ₐ.r1_of_sub_r0₀
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r0 t0 t1 h):
  (amms.sub_r0 t0 t1 h x h').r1₀ t0 t1
  =
  amms.r1₀ t0 t1
  := by simp [sub_r0]

@[simp] theorem 𝕊ₐ.r0_of_sub_r0_diff₀
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r0 t0 t1 h) (t0' t1': 𝕋) (hdiff: diffmint t0 t1 t0' t1'):
  (amms.sub_r0 t0 t1 h x h').r0₀ t0' t1'
  =
  amms.r0₀ t0' t1'
  := by simp [sub_r0, hdiff]

@[simp] theorem 𝕊ₐ.r0_of_sub_r1_diff₀
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r1 t0 t1 h)
  (t0' t1': 𝕋)
  (hdiff: diffmint t0 t1 t0' t1'):
  (amms.sub_r1 t0 t1 h x h').r0₀ t0' t1'
  =
  amms.r0₀ t0' t1'
  := by simp [sub_r1, hdiff]

@[simp] theorem 𝕊ₐ.r1_of_sub_r1_diff₀
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r1 t0 t1 h) (t0' t1': 𝕋)
  (hdiff: diffmint t0 t1 t0' t1'):
  (amms.sub_r1 t0 t1 h x h').r1₀ t0' t1'
  =
  amms.r1₀ t0' t1'
  := by simp [sub_r1, hdiff]

@[simp] theorem 𝕊ₐ.r1_of_sub_r0_diff₀
  (amms: 𝕊ₐ) (t0 t1: 𝕋) (h: amms.init t0 t1) (x: ℝ+) (h': x < amms.r0 t0 t1 h) (t0' t1': 𝕋)
  (hdiff: diffmint t0 t1 t0' t1'):
  (amms.sub_r0 t0 t1 h x h').r1₀ t0' t1'
  =
  amms.r1₀ t0' t1'
  := by simp [sub_r0, hdiff]

theorem 𝕊ₐ.eq_iff (amms amms': 𝕊ₐ): 
  amms = amms' ↔ ∀ (t0 t1: 𝕋), amms.r0₀ t0 t1 = amms'.r0₀ t0 t1 := by
  apply Iff.intro
  . intro eq t0 t1
    simp_rw [eq]
  . intro extfun
    rcases amms with ⟨f, h1, h2⟩ 
    rcases amms' with ⟨f', h1', h2'⟩
    unfold r0₀ at extfun
    simp at extfun
    simp 
    ext t0 t1
    rw [NNReal.coe_eq]
    exact extfun t0 t1