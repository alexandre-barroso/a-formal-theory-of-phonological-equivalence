import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_045
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_3687 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3688 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3689 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3676 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3677
  · exact partG37c_7_3678
  · exact partG37c_7_3679
  · exact partG37c_7_3680
  · exact partG37c_7_3681
  · exact partG37c_7_3682
  · exact partG37c_7_3683
  · exact partG37c_7_3684
  · exact partG37c_7_3685
  · exact partG37c_7_3686
  · exact partG37c_7_3687
  · exact partG37c_7_3688
  · exact partG37c_7_3689
theorem partG37c_7_3675 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3676
theorem partG37c_7_3690 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3691 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3692 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3693 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3696 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3697 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3698 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3699 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3700 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3701 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3702 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3703 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3704 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3705 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3706 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3707 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3708 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3695 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3696
  · exact partG37c_7_3697
  · exact partG37c_7_3698
  · exact partG37c_7_3699
  · exact partG37c_7_3700
  · exact partG37c_7_3701
  · exact partG37c_7_3702
  · exact partG37c_7_3703
  · exact partG37c_7_3704
  · exact partG37c_7_3705
  · exact partG37c_7_3706
  · exact partG37c_7_3707
  · exact partG37c_7_3708
theorem partG37c_7_3694 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3695
theorem partG37c_7_3709 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3654 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3655
  · exact partG37c_7_3670
  · exact partG37c_7_3671
  · exact partG37c_7_3672
  · exact partG37c_7_3673
  · exact partG37c_7_3674
  · exact partG37c_7_3675
  · exact partG37c_7_3690
  · exact partG37c_7_3691
  · exact partG37c_7_3692
  · exact partG37c_7_3693
  · exact partG37c_7_3694
  · exact partG37c_7_3709
theorem partG37c_7_2981 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2982
  · exact partG37c_7_3038
  · exact partG37c_7_3094
  · exact partG37c_7_3150
  · exact partG37c_7_3206
  · exact partG37c_7_3262
  · exact partG37c_7_3318
  · exact partG37c_7_3374
  · exact partG37c_7_3430
  · exact partG37c_7_3486
  · exact partG37c_7_3542
  · exact partG37c_7_3598
  · exact partG37c_7_3654
theorem partG37c_7_2980 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partG37c_7_2981
theorem partG37c_7_3713 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3714 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3715 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3716 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3717 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3718 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3721 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3722 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3723 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3724 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3725 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3726 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3727 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3728 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3729 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3730 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3731 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3732 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3733 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3720 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3721
  · exact partG37c_7_3722
  · exact partG37c_7_3723
  · exact partG37c_7_3724
  · exact partG37c_7_3725
  · exact partG37c_7_3726
  · exact partG37c_7_3727
  · exact partG37c_7_3728
  · exact partG37c_7_3729
  · exact partG37c_7_3730
  · exact partG37c_7_3731
  · exact partG37c_7_3732
  · exact partG37c_7_3733
theorem partG37c_7_3719 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3720
theorem partG37c_7_3734 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3735 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3736 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3737 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3738 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3739 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3712 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3713
  · exact partG37c_7_3714
  · exact partG37c_7_3715
  · exact partG37c_7_3716
  · exact partG37c_7_3717
  · exact partG37c_7_3718
  · exact partG37c_7_3719
  · exact partG37c_7_3734
  · exact partG37c_7_3735
  · exact partG37c_7_3736
  · exact partG37c_7_3737
  · exact partG37c_7_3738
  · exact partG37c_7_3739
theorem partG37c_7_3743 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3744 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3745 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3746 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3747 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3748 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3749 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3750 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3751 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3752 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3753 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3754 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3755 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3742 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3743
  · exact partG37c_7_3744
  · exact partG37c_7_3745
  · exact partG37c_7_3746
  · exact partG37c_7_3747
  · exact partG37c_7_3748
  · exact partG37c_7_3749
  · exact partG37c_7_3750
  · exact partG37c_7_3751
  · exact partG37c_7_3752
  · exact partG37c_7_3753
  · exact partG37c_7_3754
  · exact partG37c_7_3755
theorem partG37c_7_3741 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3742
theorem partG37c_7_3756 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3757 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3758 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3759 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3760 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3763 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3764 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3765 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3766 : check uG37c (3) (0) outG37c ["ɔ","tʃ","i","s","a","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
