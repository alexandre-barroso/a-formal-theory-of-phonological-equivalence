import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_022
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_1847 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1848 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1849 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1850 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1851 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1852 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1853 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1854 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1855 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1856 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1843 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1844
  · exact partG37c_7_1845
  · exact partG37c_7_1846
  · exact partG37c_7_1847
  · exact partG37c_7_1848
  · exact partG37c_7_1849
  · exact partG37c_7_1850
  · exact partG37c_7_1851
  · exact partG37c_7_1852
  · exact partG37c_7_1853
  · exact partG37c_7_1854
  · exact partG37c_7_1855
  · exact partG37c_7_1856
theorem partG37c_7_1842 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1843
theorem partG37c_7_1857 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1802 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1803
  · exact partG37c_7_1818
  · exact partG37c_7_1819
  · exact partG37c_7_1820
  · exact partG37c_7_1821
  · exact partG37c_7_1822
  · exact partG37c_7_1823
  · exact partG37c_7_1838
  · exact partG37c_7_1839
  · exact partG37c_7_1840
  · exact partG37c_7_1841
  · exact partG37c_7_1842
  · exact partG37c_7_1857
theorem partG37c_7_1861 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1862 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1863 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1864 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1865 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1866 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1867 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1868 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1869 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1870 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1871 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1872 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1873 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1860 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1861
  · exact partG37c_7_1862
  · exact partG37c_7_1863
  · exact partG37c_7_1864
  · exact partG37c_7_1865
  · exact partG37c_7_1866
  · exact partG37c_7_1867
  · exact partG37c_7_1868
  · exact partG37c_7_1869
  · exact partG37c_7_1870
  · exact partG37c_7_1871
  · exact partG37c_7_1872
  · exact partG37c_7_1873
theorem partG37c_7_1859 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1860
theorem partG37c_7_1874 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1875 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1876 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1877 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1878 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1881 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1882 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1883 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1884 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1885 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1886 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1887 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1888 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1889 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1890 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1891 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1892 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1893 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1880 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1881
  · exact partG37c_7_1882
  · exact partG37c_7_1883
  · exact partG37c_7_1884
  · exact partG37c_7_1885
  · exact partG37c_7_1886
  · exact partG37c_7_1887
  · exact partG37c_7_1888
  · exact partG37c_7_1889
  · exact partG37c_7_1890
  · exact partG37c_7_1891
  · exact partG37c_7_1892
  · exact partG37c_7_1893
theorem partG37c_7_1879 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1880
theorem partG37c_7_1894 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1895 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1896 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1897 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1900 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1901 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1902 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1903 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1904 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1905 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1906 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1907 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1908 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1909 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1910 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1911 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1912 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1899 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1900
  · exact partG37c_7_1901
  · exact partG37c_7_1902
  · exact partG37c_7_1903
  · exact partG37c_7_1904
  · exact partG37c_7_1905
  · exact partG37c_7_1906
  · exact partG37c_7_1907
  · exact partG37c_7_1908
  · exact partG37c_7_1909
  · exact partG37c_7_1910
  · exact partG37c_7_1911
  · exact partG37c_7_1912
theorem partG37c_7_1898 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1899
theorem partG37c_7_1913 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1858 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1859
  · exact partG37c_7_1874
  · exact partG37c_7_1875
  · exact partG37c_7_1876
  · exact partG37c_7_1877
  · exact partG37c_7_1878
  · exact partG37c_7_1879
  · exact partG37c_7_1894
  · exact partG37c_7_1895
  · exact partG37c_7_1896
  · exact partG37c_7_1897
  · exact partG37c_7_1898
  · exact partG37c_7_1913
theorem partG37c_7_1917 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1918 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1919 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1920 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1921 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1922 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1923 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1924 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1925 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1926 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
