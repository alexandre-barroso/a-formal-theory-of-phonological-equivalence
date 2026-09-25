import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_044
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_3607 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3608 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3609 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3610 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3611 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3612 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3613 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3600 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3601
  · exact partG37c_7_3602
  · exact partG37c_7_3603
  · exact partG37c_7_3604
  · exact partG37c_7_3605
  · exact partG37c_7_3606
  · exact partG37c_7_3607
  · exact partG37c_7_3608
  · exact partG37c_7_3609
  · exact partG37c_7_3610
  · exact partG37c_7_3611
  · exact partG37c_7_3612
  · exact partG37c_7_3613
theorem partG37c_7_3599 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3600
theorem partG37c_7_3614 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3615 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3616 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3617 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3618 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3621 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3622 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3623 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3624 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3625 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3626 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3627 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3628 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3629 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3630 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3631 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3632 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3633 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3620 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3621
  · exact partG37c_7_3622
  · exact partG37c_7_3623
  · exact partG37c_7_3624
  · exact partG37c_7_3625
  · exact partG37c_7_3626
  · exact partG37c_7_3627
  · exact partG37c_7_3628
  · exact partG37c_7_3629
  · exact partG37c_7_3630
  · exact partG37c_7_3631
  · exact partG37c_7_3632
  · exact partG37c_7_3633
theorem partG37c_7_3619 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3620
theorem partG37c_7_3634 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3635 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3636 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3637 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3640 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3641 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3642 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3643 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3644 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3645 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3646 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3647 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3648 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3649 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3650 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3651 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3652 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3639 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3640
  · exact partG37c_7_3641
  · exact partG37c_7_3642
  · exact partG37c_7_3643
  · exact partG37c_7_3644
  · exact partG37c_7_3645
  · exact partG37c_7_3646
  · exact partG37c_7_3647
  · exact partG37c_7_3648
  · exact partG37c_7_3649
  · exact partG37c_7_3650
  · exact partG37c_7_3651
  · exact partG37c_7_3652
theorem partG37c_7_3638 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3639
theorem partG37c_7_3653 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3598 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3599
  · exact partG37c_7_3614
  · exact partG37c_7_3615
  · exact partG37c_7_3616
  · exact partG37c_7_3617
  · exact partG37c_7_3618
  · exact partG37c_7_3619
  · exact partG37c_7_3634
  · exact partG37c_7_3635
  · exact partG37c_7_3636
  · exact partG37c_7_3637
  · exact partG37c_7_3638
  · exact partG37c_7_3653
theorem partG37c_7_3657 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3658 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3659 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3660 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3661 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3662 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3663 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3664 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3665 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3666 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3667 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3668 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3669 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3656 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3657
  · exact partG37c_7_3658
  · exact partG37c_7_3659
  · exact partG37c_7_3660
  · exact partG37c_7_3661
  · exact partG37c_7_3662
  · exact partG37c_7_3663
  · exact partG37c_7_3664
  · exact partG37c_7_3665
  · exact partG37c_7_3666
  · exact partG37c_7_3667
  · exact partG37c_7_3668
  · exact partG37c_7_3669
theorem partG37c_7_3655 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3656
theorem partG37c_7_3670 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3671 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3672 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3673 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3674 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3677 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3678 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3679 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3680 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3681 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3682 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3683 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3684 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3685 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3686 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
