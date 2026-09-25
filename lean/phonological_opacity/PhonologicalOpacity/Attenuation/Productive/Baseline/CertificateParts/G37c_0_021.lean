import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_0_020
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_0_1687 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1688 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1689 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1690 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1691 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1692 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1693 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1694 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1695 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1696 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1697 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1684 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1685
  · exact partG37c_0_1686
  · exact partG37c_0_1687
  · exact partG37c_0_1688
  · exact partG37c_0_1689
  · exact partG37c_0_1690
  · exact partG37c_0_1691
  · exact partG37c_0_1692
  · exact partG37c_0_1693
  · exact partG37c_0_1694
  · exact partG37c_0_1695
  · exact partG37c_0_1696
  · exact partG37c_0_1697
theorem partG37c_0_1683 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_1684
theorem partG37c_0_1698 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1699 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1700 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1701 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1704 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1705 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1706 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1707 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1708 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1709 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1710 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1711 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1712 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1713 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1714 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1715 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1716 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1703 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1704
  · exact partG37c_0_1705
  · exact partG37c_0_1706
  · exact partG37c_0_1707
  · exact partG37c_0_1708
  · exact partG37c_0_1709
  · exact partG37c_0_1710
  · exact partG37c_0_1711
  · exact partG37c_0_1712
  · exact partG37c_0_1713
  · exact partG37c_0_1714
  · exact partG37c_0_1715
  · exact partG37c_0_1716
theorem partG37c_0_1702 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_1703
theorem partG37c_0_1717 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1662 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1663
  · exact partG37c_0_1678
  · exact partG37c_0_1679
  · exact partG37c_0_1680
  · exact partG37c_0_1681
  · exact partG37c_0_1682
  · exact partG37c_0_1683
  · exact partG37c_0_1698
  · exact partG37c_0_1699
  · exact partG37c_0_1700
  · exact partG37c_0_1701
  · exact partG37c_0_1702
  · exact partG37c_0_1717
theorem partG37c_0_1719 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1720 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1721 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1722 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1723 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1724 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1727 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1728 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1729 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1730 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1731 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1732 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1733 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1734 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1735 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1736 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1737 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1738 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1739 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1726 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1727
  · exact partG37c_0_1728
  · exact partG37c_0_1729
  · exact partG37c_0_1730
  · exact partG37c_0_1731
  · exact partG37c_0_1732
  · exact partG37c_0_1733
  · exact partG37c_0_1734
  · exact partG37c_0_1735
  · exact partG37c_0_1736
  · exact partG37c_0_1737
  · exact partG37c_0_1738
  · exact partG37c_0_1739
theorem partG37c_0_1725 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_1726
theorem partG37c_0_1740 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1741 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1742 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1743 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1744 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1745 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1718 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1719
  · exact partG37c_0_1720
  · exact partG37c_0_1721
  · exact partG37c_0_1722
  · exact partG37c_0_1723
  · exact partG37c_0_1724
  · exact partG37c_0_1725
  · exact partG37c_0_1740
  · exact partG37c_0_1741
  · exact partG37c_0_1742
  · exact partG37c_0_1743
  · exact partG37c_0_1744
  · exact partG37c_0_1745
theorem partG37c_0_1749 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɔ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1750 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɔ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1751 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɔ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1752 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɔ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1753 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɔ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1754 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɔ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1755 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɔ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1756 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɔ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1757 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɔ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1758 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɔ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1759 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɔ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1760 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɔ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1761 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɔ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1748 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɔ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1749
  · exact partG37c_0_1750
  · exact partG37c_0_1751
  · exact partG37c_0_1752
  · exact partG37c_0_1753
  · exact partG37c_0_1754
  · exact partG37c_0_1755
  · exact partG37c_0_1756
  · exact partG37c_0_1757
  · exact partG37c_0_1758
  · exact partG37c_0_1759
  · exact partG37c_0_1760
  · exact partG37c_0_1761
theorem partG37c_0_1747 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɔ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_1748
theorem partG37c_0_1762 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɔ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1763 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɔ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1764 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɔ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
