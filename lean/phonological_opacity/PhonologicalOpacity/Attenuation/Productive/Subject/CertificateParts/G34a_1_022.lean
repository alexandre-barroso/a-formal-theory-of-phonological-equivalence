import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G34a_1_021
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG34a_1_1768 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","∅","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1769 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","∅","k","p","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1770 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","∅","k","p","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1771 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","∅","k","p","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1758 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","∅","k","p"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_1759
  · exact partG34a_1_1760
  · exact partG34a_1_1761
  · exact partG34a_1_1762
  · exact partG34a_1_1763
  · exact partG34a_1_1764
  · exact partG34a_1_1765
  · exact partG34a_1_1766
  · exact partG34a_1_1767
  · exact partG34a_1_1768
  · exact partG34a_1_1769
  · exact partG34a_1_1770
  · exact partG34a_1_1771
theorem partG34a_1_1757 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","∅","k"] [["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="p" := by simpa using hx
  subst x
  exact partG34a_1_1758
theorem partG34a_1_1756 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","∅"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="k" := by simpa using hx
  subst x
  exact partG34a_1_1757
theorem partG34a_1_1772 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","a"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1773 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","ɜ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1774 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","ɛ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1775 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","e"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1776 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","ɪ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1777 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","i"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1781 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","ɔ","k","p","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1782 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","ɔ","k","p","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1783 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","ɔ","k","p","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1784 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","ɔ","k","p","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1785 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","ɔ","k","p","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1786 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","ɔ","k","p","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1787 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","ɔ","k","p","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1788 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","ɔ","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1789 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","ɔ","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1790 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","ɔ","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1791 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","ɔ","k","p","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1792 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","ɔ","k","p","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1793 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","ɔ","k","p","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1780 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","ɔ","k","p"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_1781
  · exact partG34a_1_1782
  · exact partG34a_1_1783
  · exact partG34a_1_1784
  · exact partG34a_1_1785
  · exact partG34a_1_1786
  · exact partG34a_1_1787
  · exact partG34a_1_1788
  · exact partG34a_1_1789
  · exact partG34a_1_1790
  · exact partG34a_1_1791
  · exact partG34a_1_1792
  · exact partG34a_1_1793
theorem partG34a_1_1779 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","ɔ","k"] [["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="p" := by simpa using hx
  subst x
  exact partG34a_1_1780
theorem partG34a_1_1778 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","ɔ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="k" := by simpa using hx
  subst x
  exact partG34a_1_1779
theorem partG34a_1_1794 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","o"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1795 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","ʊ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1796 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","u"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1797 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","j"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1798 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u","w"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1755 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_1756
  · exact partG34a_1_1772
  · exact partG34a_1_1773
  · exact partG34a_1_1774
  · exact partG34a_1_1775
  · exact partG34a_1_1776
  · exact partG34a_1_1777
  · exact partG34a_1_1778
  · exact partG34a_1_1794
  · exact partG34a_1_1795
  · exact partG34a_1_1796
  · exact partG34a_1_1797
  · exact partG34a_1_1798
theorem partG34a_1_1800 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","∅"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1801 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","a"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1802 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","ɜ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1803 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","ɛ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1804 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","e"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1805 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","ɪ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1806 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","i"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1810 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","ɔ","k","p","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1811 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","ɔ","k","p","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1812 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","ɔ","k","p","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1813 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","ɔ","k","p","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1814 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","ɔ","k","p","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1815 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","ɔ","k","p","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1816 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","ɔ","k","p","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1817 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","ɔ","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1818 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","ɔ","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1819 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","ɔ","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1820 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","ɔ","k","p","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1821 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","ɔ","k","p","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1822 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","ɔ","k","p","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1809 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","ɔ","k","p"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_1810
  · exact partG34a_1_1811
  · exact partG34a_1_1812
  · exact partG34a_1_1813
  · exact partG34a_1_1814
  · exact partG34a_1_1815
  · exact partG34a_1_1816
  · exact partG34a_1_1817
  · exact partG34a_1_1818
  · exact partG34a_1_1819
  · exact partG34a_1_1820
  · exact partG34a_1_1821
  · exact partG34a_1_1822
theorem partG34a_1_1808 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","ɔ","k"] [["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="p" := by simpa using hx
  subst x
  exact partG34a_1_1809
theorem partG34a_1_1807 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","ɔ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="k" := by simpa using hx
  subst x
  exact partG34a_1_1808
theorem partG34a_1_1823 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","o"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1824 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","ʊ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1825 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","u"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1826 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","j"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1827 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j","w"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1799 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_1800
  · exact partG34a_1_1801
  · exact partG34a_1_1802
  · exact partG34a_1_1803
  · exact partG34a_1_1804
  · exact partG34a_1_1805
  · exact partG34a_1_1806
  · exact partG34a_1_1807
  · exact partG34a_1_1823
  · exact partG34a_1_1824
  · exact partG34a_1_1825
  · exact partG34a_1_1826
  · exact partG34a_1_1827
theorem partG34a_1_1829 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","w","∅"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1830 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","w","a"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1831 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","w","ɜ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1832 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","w","ɛ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1833 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","w","e"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1834 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","w","ɪ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1835 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","w","i"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1839 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","w","ɔ","k","p","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1840 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","w","ɔ","k","p","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1841 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","w","ɔ","k","p","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1842 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","w","ɔ","k","p","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1843 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","w","ɔ","k","p","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1844 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","w","ɔ","k","p","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1845 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","w","ɔ","k","p","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1846 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","w","ɔ","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1847 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","w","ɔ","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
