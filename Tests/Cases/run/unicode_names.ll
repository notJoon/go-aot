@.int_format = private unnamed_addr constant [6 x i8] c"%lld\0A\00"
@.true = private unnamed_addr constant [5 x i8] c"true\00"
@.false = private unnamed_addr constant [6 x i8] c"false\00"
@.nan = private unnamed_addr constant [4 x i8] c"NaN\00"
@.plus_infinity = private unnamed_addr constant [5 x i8] c"+Inf\00"
@.minus_infinity = private unnamed_addr constant [5 x i8] c"-Inf\00"
@.float_digits = private unnamed_addr constant [5 x i8] c"%.*e\00"
@.float_scientific = private unnamed_addr constant [6 x i8] c"%.*e\0A\00"
@.float_fixed = private unnamed_addr constant [6 x i8] c"%.*f\0A\00"

declare i32 @printf(ptr, ...)
declare i32 @puts(ptr)
declare i32 @snprintf(ptr, i64, ptr, ...)
declare double @strtod(ptr, ptr)
declare ptr @strchr(ptr, i32)
declare i64 @strtol(ptr, ptr, i32)
declare double @llvm.fabs.f64(double)

define internal void @goaot.print_float(double %value) {
entry:
  %buffer = alloca [32 x i8]
  %nan = fcmp uno double %value, %value
  br i1 %nan, label %print_nan, label %check_infinity

print_nan:
  call i32 @puts(ptr @.nan)
  ret void

check_infinity:
  %magnitude = call double @llvm.fabs.f64(double %value)
  %infinite = fcmp oeq double %magnitude, 0x7FF0000000000000
  br i1 %infinite, label %print_infinity, label %search

print_infinity:
  %positive = fcmp ogt double %value, 0.0
  %text = select i1 %positive, ptr @.plus_infinity, ptr @.minus_infinity
  call i32 @puts(ptr %text)
  ret void

search:
  br label %loop

loop:
  %precision = phi i32 [ 0, %search ], [ %next, %retry ]
  call i32 (ptr, i64, ptr, ...) @snprintf(ptr %buffer, i64 32, ptr @.float_digits, i32 %precision, double %value)
  %parsed = call double @strtod(ptr %buffer, ptr null)
  %exact = fcmp oeq double %parsed, %value
  %last = icmp eq i32 %precision, 16
  %done = or i1 %exact, %last
  br i1 %done, label %format, label %retry

retry:
  %next = add i32 %precision, 1
  br label %loop

format:
  %marker = call ptr @strchr(ptr %buffer, i32 101)
  %exponent.text = getelementptr i8, ptr %marker, i64 1
  %exponent = call i64 @strtol(ptr %exponent.text, ptr null, i32 10)
  %small = icmp slt i64 %exponent, -4
  %large = icmp sge i64 %exponent, 6
  %scientific = or i1 %small, %large
  br i1 %scientific, label %print_scientific, label %print_fixed

print_scientific:
  call i32 (ptr, ...) @printf(ptr @.float_scientific, i32 %precision, double %value)
  ret void

print_fixed:
  %precision.wide = sext i32 %precision to i64
  %fraction = sub i64 %precision.wide, %exponent
  %whole = icmp slt i64 %fraction, 0
  %fraction.clamped = select i1 %whole, i64 0, i64 %fraction
  %fraction.narrow = trunc i64 %fraction.clamped to i32
  call i32 (ptr, ...) @printf(ptr @.float_fixed, i32 %fraction.narrow, double %value)
  ret void
}

define internal i64 @"go_\EA\B3\84\EC\82\B0"(i64 %arg0) {
bb0:
  %slot0 = alloca i64
  %slot1 = alloca i64
  store i64 %arg0, ptr %slot0
  %v0 = load i64, ptr %slot0
  %v1 = mul i64 %v0, 2
  store i64 %v1, ptr %slot1
  %v2 = load i64, ptr %slot1
  ret i64 %v2
}

define internal { double, i1 } @"go_n\C3\A5de"(double %arg0) {
bb0:
  %slot0 = alloca double
  store double %arg0, ptr %slot0
  %v0 = load double, ptr %slot0
  %v1 = load double, ptr %slot0
  %v2 = fcmp ogt double %v1, 0x4008000000000000
  %ret0.0 = insertvalue { double, i1 } poison, double %v0, 0
  %ret0.1 = insertvalue { double, i1 } %ret0.0, i1 %v2, 1
  ret { double, i1 } %ret0.1
}

define i32 @main() {
bb0:
  %slot0 = alloca double
  %slot1 = alloca i1
  %v0 = call i64 @"go_\EA\B3\84\EC\82\B0"(i64 21)
  call i32 (ptr, ...) @printf(ptr @.int_format, i64 %v0)
  %results1 = call { double, i1 } @"go_n\C3\A5de"(double 0x400C000000000000)
  %v1 = extractvalue { double, i1 } %results1, 0
  %v2 = extractvalue { double, i1 } %results1, 1
  store double %v1, ptr %slot0
  store i1 %v2, ptr %slot1
  %v3 = load double, ptr %slot0
  call void @goaot.print_float(double %v3)
  %v4 = load i1, ptr %slot1
  %print0.10 = select i1 %v4, ptr @.true, ptr @.false
  call i32 @puts(ptr %print0.10)
  ret i32 0
}
