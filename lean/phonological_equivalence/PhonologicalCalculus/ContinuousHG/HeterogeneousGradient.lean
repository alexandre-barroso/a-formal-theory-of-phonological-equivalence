                            
import PhonologicalCalculus.ContinuousHG.HeterogeneousFibers
namespace PhonologicalCalculus.ContinuousHG.HeterogeneousCubeBridge
open Finset HeterogeneousProfileBridge
theorem reduced_directional_derivative {N : ℕ} (h p : ℝ) (m d v : Fin N → ℝ)
    (hp : 1 < p) :
    HasDerivAt (fun t : ℝ => powerReducedObjective h 1 p (suffixWeight m) (fun i => d i+t*v i))
      (∑ i : Fin N, powerGradient h 1 p (suffixWeight m) d i * v i) 0 := by
  have hi : ∀ i : Fin N, HasDerivAt (fun t : ℝ => h*(d i+t*v i)^p - suffixWeight m i*(d i+t*v i))
      (powerGradient h 1 p (suffixWeight m) d i * v i) 0 := by
    intro i
    have hl : HasDerivAt (fun t : ℝ => d i+t*v i) (v i) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const (v i)).const_add (d i)
    have hr := (Real.hasDerivAt_rpow_const (x:=d i+0*v i) (p:=p) (Or.inr hp.le)).comp 0 hl
    have hc := (hr.const_mul h).sub (hl.const_mul (suffixWeight m i))
    convert hc using 1
    all_goals first | rfl | (simp only [powerGradient, zero_mul, add_zero, one_mul]; ring)
  simpa only [powerReducedObjective, one_mul] using HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => hi i)

end PhonologicalCalculus.ContinuousHG.HeterogeneousCubeBridge
