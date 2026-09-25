import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.OR38_1_007
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_1_645 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɜ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_646 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɜ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_647 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɜ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_648 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɜ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_649 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɜ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_650 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɜ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_651 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɜ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_652 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɜ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_653 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɜ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_640 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_641
  · exact partOR38_1_642
  · exact partOR38_1_643
  · exact partOR38_1_644
  · exact partOR38_1_645
  · exact partOR38_1_646
  · exact partOR38_1_647
  · exact partOR38_1_648
  · exact partOR38_1_649
  · exact partOR38_1_650
  · exact partOR38_1_651
  · exact partOR38_1_652
  · exact partOR38_1_653
theorem partOR38_1_655 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɛ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_656 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɛ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_657 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɛ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_658 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɛ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_659 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɛ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_660 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɛ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_661 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɛ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_662 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɛ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_663 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɛ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_664 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɛ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_665 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɛ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_666 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɛ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_667 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɛ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_654 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_655
  · exact partOR38_1_656
  · exact partOR38_1_657
  · exact partOR38_1_658
  · exact partOR38_1_659
  · exact partOR38_1_660
  · exact partOR38_1_661
  · exact partOR38_1_662
  · exact partOR38_1_663
  · exact partOR38_1_664
  · exact partOR38_1_665
  · exact partOR38_1_666
  · exact partOR38_1_667
theorem partOR38_1_669 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","e","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_670 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","e","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_671 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","e","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_672 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","e","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_673 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","e","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_674 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","e","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_675 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","e","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_676 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","e","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_677 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","e","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_678 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","e","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_679 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","e","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_680 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","e","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_681 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","e","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_668 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_669
  · exact partOR38_1_670
  · exact partOR38_1_671
  · exact partOR38_1_672
  · exact partOR38_1_673
  · exact partOR38_1_674
  · exact partOR38_1_675
  · exact partOR38_1_676
  · exact partOR38_1_677
  · exact partOR38_1_678
  · exact partOR38_1_679
  · exact partOR38_1_680
  · exact partOR38_1_681
theorem partOR38_1_683 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɪ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_684 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɪ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_685 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɪ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_686 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɪ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_687 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɪ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_688 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɪ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_689 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɪ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_690 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɪ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_691 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɪ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_692 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɪ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_693 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɪ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_694 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɪ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_695 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɪ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_682 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_683
  · exact partOR38_1_684
  · exact partOR38_1_685
  · exact partOR38_1_686
  · exact partOR38_1_687
  · exact partOR38_1_688
  · exact partOR38_1_689
  · exact partOR38_1_690
  · exact partOR38_1_691
  · exact partOR38_1_692
  · exact partOR38_1_693
  · exact partOR38_1_694
  · exact partOR38_1_695
theorem partOR38_1_697 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","i","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_698 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","i","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_699 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","i","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_700 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","i","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_701 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","i","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_702 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","i","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_703 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","i","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_704 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","i","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_705 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","i","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_706 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","i","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_707 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","i","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_708 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","i","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_709 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","i","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_696 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_697
  · exact partOR38_1_698
  · exact partOR38_1_699
  · exact partOR38_1_700
  · exact partOR38_1_701
  · exact partOR38_1_702
  · exact partOR38_1_703
  · exact partOR38_1_704
  · exact partOR38_1_705
  · exact partOR38_1_706
  · exact partOR38_1_707
  · exact partOR38_1_708
  · exact partOR38_1_709
theorem partOR38_1_711 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɔ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_712 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɔ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_713 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɔ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_714 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɔ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_715 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɔ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_716 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɔ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_717 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɔ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_718 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɔ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_719 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɔ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_720 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɔ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_721 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɔ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_722 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɔ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_723 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɔ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_710 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_711
  · exact partOR38_1_712
  · exact partOR38_1_713
  · exact partOR38_1_714
  · exact partOR38_1_715
  · exact partOR38_1_716
  · exact partOR38_1_717
  · exact partOR38_1_718
  · exact partOR38_1_719
  · exact partOR38_1_720
  · exact partOR38_1_721
  · exact partOR38_1_722
  · exact partOR38_1_723
end ProductiveSubjectGua
