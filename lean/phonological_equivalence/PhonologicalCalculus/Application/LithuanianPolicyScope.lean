                          
import PhonologicalCalculus.Application.LithuanianEncodings

namespace LithuanianPolicyScope

open LithuanianEncodings

def UniformPolicy (ma mn : Mode) : Prop := ma = .origin ↔ mn = .origin

theorem uniform_excludes_counterbleeding (ma mn : Mode) (c r d a n l : ℝ)
    (hc : 0≤c) (hr : 0≤r) (hd : 0≤d) (ha : 0≤a) (hn : 0≤n) (hl : 0≤l)
    (hu : UniformPolicy ma mn) : ¬ Selective ma mn .counterbleeding c r d a n l := by
  intro h
  have hrgn := (exact_regions ma mn .counterbleeding c r d a n l hc hr hd ha hn hl).mp h
  cases ma <;> cases mn <;> simp_all [Region, UniformPolicy]

theorem uniform_positive_nonempty (l : ℝ) (hl : 0<l) :
    UniformPolicy .relational .relational ∧
    Selective .relational .relational .positive 1 4 2 (4+3/l) (4+3/l) l :=
  ⟨Iff.rfl, positive_witness l hl⟩

theorem counterbleeding_requires_nonuniform (ma mn : Mode) (c r d a n l : ℝ)
    (hc : 0≤c) (hr : 0≤r) (hd : 0≤d) (ha : 0≤a) (hn : 0≤n) (hl : 0≤l)
    (h : Selective ma mn .counterbleeding c r d a n l) : ¬ UniformPolicy ma mn := by
  intro hu
  exact uniform_excludes_counterbleeding ma mn c r d a n l hc hr hd ha hn hl hu h

end LithuanianPolicyScope
