module

public import Compiler.Source
public import Compiler.Compile

/- Compiler.* modules are internal interfaces available only through direct imports.
   Applications should use Source and compileToC / compileToLLVM. -/
