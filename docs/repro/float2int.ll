define i1 @f() {
  %1 = fmul double 0xD28BC4DE7363B01B, 0xD28BC4DE7363B01B
  %2 = fcmp ugt double %1, 0.000000e+00
  ret i1 %2
}
define i1 @g() {
  %1 = fmul double 0xD28BC4DE7363B01B, 0xD28BC4DE7363B01B
  %2 = fcmp ogt double %1, 0.000000e+00
  ret i1 %2
}
define i1 @h() {
  %1 = fmul double 1.0e+30, 1.0e+30
  %2 = fcmp ogt double %1, 0.000000e+00
  ret i1 %2
}
define i1 @k() {
  %1 = fmul double 3.0e+9, 3.0e+9
  %2 = fcmp ogt double %1, 0.000000e+00
  ret i1 %2
}
define i1 @a() {
  %1 = fadd double 1.0e+30, 1.0e+30
  %2 = fcmp ogt double %1, 1.0
  ret i1 %2
}
