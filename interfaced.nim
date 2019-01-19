## Go-Like Interfaces for Nim
##
## The idea is from Krux02
## https://forum.nim-lang.org/t/2422

import macros, strutils

const
  MAX_IMPLEMENTS = 32

type
  InterfaceInfo = ref object
    inf: NimNode          # interface symbol
    created: bool         # interface converter created
    exported: bool        # interface is global
    inherited: NimNode    # inherited symbol
    impls: seq[NimNode]   # implmentation symbol

var
  iinfos {.compileTime}: seq[InterfaceInfo] = @[]

template InterfaceId*(val: int) {.pragma.}

proc remove_postfix(n: NimNode): NimNode =
  if n.kind == nnkPostfix: n[1] else: n

proc export_postfix(n: NimNode, exported = true): NimNode =
  if exported: postfix(n, "*") else: n

proc unpack_varty(typ: NimNode): NimNode =
  if typ.kind == nnkVarTy: typ[0] else: typ

proc is_tostring_method(method_name, params: NimNode): bool =
  method_name.kind == nnkAccQuoted and $method_name == "$" and
    params.len == 2 and params[1].len == 3

proc get_interface_id(inf: NimNode): int =
  inf.getImpl[0][1][0][1].intVal.int

proc add_interface_info(inherited: NimNode, exported: bool): int =
  iinfos.add InterfaceInfo(inherited: inherited.copy, exported: exported)
  iinfos.len-1

proc set_interface_self(inf: NimNode) =
  let id = get_interface_id(inf)
  assert id >= 0
  iinfos[id].inf = inf.copy

proc is_interface_exported(inf: NimNode): bool =
  let id = get_interface_id(inf)
  assert id >= 0
  iinfos[id].exported

proc get_interface_base(inf: NimNode): NimNode =
  let id = get_interface_id(inf)
  assert id >= 0
  iinfos[id].inherited

proc get_interface_base_count(inf: NimNode): int =
  let id = get_interface_id(inf)
  assert id >= 0
  iinfos[id].inherited.len

template has_interface_bases(inf: NimNode): bool =
  get_interface_base_count(inf) > 0

proc interface_converter_created(inf: NimNode): bool =
  let id = get_interface_id(inf)
  assert id >= 0
  iinfos[id].created

proc set_interface_converter_created(inf: NimNode, created = true) =
  let id = get_interface_id(inf)
  assert id >= 0
  iinfos[id].created = created

proc get_implemented_index(inf_name: NimNode, impl_name: NimNode, add_if_not_present = false): int =
  let id = get_interface_id(inf_name)
  assert id >= 0

  let info = iinfos[id]

  result = -1
  for i, imp in info.impls:
    if eqIdent(imp, impl_name):
      result = i
      break

  if result == -1 and add_if_not_present:
    info.impls.add(impl_name)
    if info.impls.len > MAX_IMPLEMENTS:
      error("Too many implments for " & $inf_name & "\nPlease change the MAX_IMPLEMENTS")
    result = info.impls.len-1

proc get_or_add_implementation(inf_name: NimNode, impl_name: NimNode): int =
  get_implemented_index(inf_name, impl_name, true)

proc add_interface_implementation(inf_name: NimNode, impl_name: NimNode) =
  discard get_implemented_index(inf_name, impl_name, true)

proc is_implemented(inf_name: NimNode, impl_name: NimNode): bool =
  get_implemented_index(inf_name, impl_name, false) >= 0

template get_vtable_symbol(inf_name: NimNode): NimNode =
  inf_name.getImpl[2][2][1][1][0]

template get_vtable_records(vtable_symbol: NimNode): NimNode =
  vtable_symbol.getImpl[2][2]

template get_vtable_records_from_interface(inf_name: NimNode): NimNode =
  inf_name.get_vtable_symbol.get_vtable_records

proc get_dispatch_table_var(inf_name: NimNode): NimNode =
  nnkAccQuoted.newTree(ident(":" & $inf_name & "_dispatch_vtables"))

proc get_dispatch_indexes_var(inf_name: NimNode): NimNode =
  nnkAccQuoted.newTree(ident(":" & $inf_name & "_dispatch_indexes"))

proc get_interface_constructor_name(inf_name: NimNode): NimNode =
  nnkAccQuoted.newTree(ident(":Create" & $inf_name))

proc get_method_name_pair(name: NimNode): tuple[prop: NimNode, name: NimNode] =
  var
    name = name.remove_postfix
    prop = name

  if name.kind == nnkAccQuoted:
    let s = $name
    if s[0] == ':':
      if s[^2].isdigit:
        name = ident(substr(s, 1, s.len-3))
      else:
        name = ident(substr(s, 1, s.len-2))
  (prop, name)

proc get_interface_bases_all(inf_name: NimNode, bases: var seq[NimNode]) =
  bases.add inf_name
  let inherited = get_interface_base(inf_name)
  for base in inherited:
    get_interface_bases_all(base, bases)

proc get_interface_bases_all(inf_name: NimNode): seq[NimNode] =
  result = @[]
  get_interface_bases_all(inf_name, result)

iterator param_pairs(params: NimNode, skip_first: bool): tuple[name: NimNode, typ: NimNode] =
  let start = if skip_first: 2 else: 1
  for i in start ..< len(params):
    let param = params[i]
    param.expectKind(nnkIdentDefs)
    for j in 0 .. len(param) - 3:
      yield (name: param[j], typ: param[^2])

proc is_same_params_type(m1, m2: NimNode): bool =
  var
    types1, types2: seq[NimNode]

  for _, typ in m1.param_pairs(false): types1.add typ
  for _, typ in m2.param_pairs(false): types2.add typ

  types1 == types2

proc add_method_checker(impl_name, inf_name: NimNode): NimNode =
  result = newStmtList()

  for ident_defs in inf_name.get_vtable_records_from_interface:
    let
      (prop, method_name) = get_method_name_pair(ident_defs[0])
      params = ident_defs[1][0]
      def_vars = newNimNode(nnkVarSection)
      meth = newCall(method_name)

    if is_tostring_method(method_name, params):
      continue

    for name, typ in param_pairs(params, false):
      def_vars.add newIdentDefs(name, typ.unpack_varty)
      meth.add name

    # change first argument type to `impl_name`
    def_vars[0][1] = impl_name

    let method_checker = newStmtList(def_vars)
    if params[0] == ident("void") or params[0].kind == nnkEmpty:
      method_checker.add meth
    else:
      # check the return value
      method_checker.add nnkLetSection.newTree(newIdentDefs(genSym(), params[0].unpack_varty, meth))

    let proc_str = "proc " & ident_defs.repr.replace("RootRef", $impl_name).replace(": proc ", "").replace("`" & $prop & "`", $method_name)
    result.add quote do:
      when not compiles(`method_checker`):
        {.fatal: "proc undefined when implements " & $`inf_name` & ":\p  " & `proc_str`.}

proc add_tostring_proc(impl_name: NimNode): NimNode =
  let method_name = nnkAccQuoted.newTree(ident("$"))
  result = quote do:
    when not compiles((var x: `impl_name`; discard $x)):
      proc `method_name`(x: `impl_name`): string = $x[]

proc get_interface_vtable(impl_name, inf_name, var_name: NimNode): NimNode =
  let
    vtable_symbol = inf_name.get_vtable_symbol

  let vtable_cons = nnkObjConstr.newTree(vtable_symbol)
  for ident_defs in vtable_symbol.get_vtable_records:
    let
      (prop, method_name) = get_method_name_pair(ident_defs[0])
      proc_type = ident_defs[1]
      real_proc_type = proc_type.copy

    real_proc_type[0][1][^2] = impl_name
    let proc_name_casted = quote do:
      cast[`proc_type`](cast[pointer]((`real_proc_type`)(`method_name`)))
    vtable_cons.add newColonExpr(prop, proc_name_casted)

  newVarStmt(var_name, vtable_cons)

proc add_method_dispatch_table(impl_name, inf_name: NimNode): NimNode =
  let
    dispatch_table = get_dispatch_table_var(inf_name)
    bases = get_interface_bases_all(inf_name)
    impl_index = get_implemented_index(inf_name, impl_name)
    vtable = genSym(nskVar)

  assert(impl_index >= 0)
  result = newStmtList()
  result.add get_interface_vtable(impl_name, inf_name, vtable)
  result.add quote do:
    `dispatch_table`[`impl_index`] = cast[pointer](addr `vtable`)

  if has_interface_bases(inf_name):
    let dispatch_indexes = get_dispatch_indexes_var(inf_name)
    for i, base in bases:
      let inf_impl_index = get_implemented_index(base, impl_name)
      assert(inf_impl_index >= 0)
      result.add quote do:
        `dispatch_indexes`[`impl_index`][`i`] = `inf_impl_index`

proc add_object_converter(impl_name, inf_name: NimNode, inf_index: int, implict_converter: bool): NimNode =
  let
    dispatch_table = get_dispatch_table_var(inf_name)
    inf_vtable = inf_name.get_vtable_symbol
    this_param = ident("self")
    impl_index = get_implemented_index(inf_name, impl_name)

  assert(impl_index >= 0)
  let constructor_name = get_interface_constructor_name(inf_name)
  let inf_constructor = quote do:
    `constructor_name`(cast[RootRef](`this_param`), cast[ptr `inf_vtable`](`dispatch_table`[`impl_index`]))

  if has_interface_bases(inf_name):
    inf_constructor.add newLit(impl_index)

  result = newStmtList()

  let cast_name = ident("to" & $inf_name)
  result.add quote do:
    proc `cast_name`*(`this_param`: `impl_name`) : `inf_name` = `inf_constructor`

  if implict_converter:
    let converter_name = ident($impl_name & "To" & $inf_name & "Converter")
    result.add quote do:
      converter `converter_name`*(`this_param`: `impl_name`) : `inf_name` = `inf_constructor`

macro impl*(impl_name: typed{type}, inf_names: varargs[typed]) : untyped =
  var
    implict_converter = true

  for inf_name in inf_names:
    if inf_name == bindSym("false"):
      implict_converter = false
      break

  result = newStmtList()
  for inf_name in inf_names:
    if inf_name in [bindSym("true"), bindSym("false")] :
      continue

    let
      bases = get_interface_bases_all(inf_name)

    result.add add_method_checker(impl_name, inf_name)
    result.add add_tostring_proc(impl_name)

    for inf_index, base in bases:
      if not is_implemented(base, impl_name):
        add_interface_implementation(base, impl_name)
        result.add add_object_converter(impl_name, base, inf_index, implict_converter)

    for base in bases:
      result.add add_method_dispatch_table(impl_name, base)

  when defined(interfacedebug):
    echo result.repr

proc create_interface_constructor(inf_name: NimNode): NimNode =
  let
    constructor_name = get_interface_constructor_name(inf_name)
    vtable = inf_name.get_vtable_symbol

  result =
    if has_interface_bases(inf_name):
      quote do:
        template `constructor_name`*(o: RootRef, v: ptr `vtable`, i: int): `inf_name` = `inf_name`(obj: o, vtable: v, impl_index: i)
    else:
      quote do:
        template `constructor_name`*(o: RootRef, v: ptr `vtable`): `inf_name` = `inf_name`(obj: o, vtable: v)

proc create_interface_method_impl(inf_name: NimNode): NimNode =
  result = newStmtList()

  for ident_defs in inf_name.get_vtable_records_from_interface:
    let
      (prop, method_name) = get_method_name_pair(ident_defs[0])
      params = ident_defs[1][0]
      this_param = params[1][0]
      meth = newProc(export_postfix(method_name), proc_type = nnkTemplateDef)

    meth.params = params
    meth.params[1][1] = ident($inf_name)

    meth.body = quote do:
      `this_param`.vtable.`prop`(`this_param`.obj)

    for name, _ in param_pairs(params, true):
      meth.body.add name

    result.add meth

proc add_dispatch_table_for_one_interface(inf_name: NimNode): NimNode =
  result = newStmtList()

  if not interface_converter_created(inf_name):
    let
      dispatch_table = get_dispatch_table_var(inf_name)

    result.add quote do:
      var
        `dispatch_table`*: array[MAX_IMPLEMENTS, pointer]

    # only create dispatch indexes when there are base interfaces
    if has_interface_bases(inf_name):
      let
        dispatch_indexes = get_dispatch_indexes_var(inf_name)
        inf_count = get_interface_bases_all(inf_name).len

      result.add quote do:
        var
          `dispatch_indexes`*: array[MAX_IMPLEMENTS, array[`inf_count`, int8]]

proc add_dispatch_table(inf_name: NimNode): NimNode =
  result = newStmtList()
  for base in get_interface_bases_all(inf_name):
    result.add add_dispatch_table_for_one_interface(base)

proc add_interface_converter(from_inf_name, inf_name: NimNode, inf_index: int): NimNode =
  let
    dispatch_table = get_dispatch_table_var(inf_name)
    dispatch_indexes = get_dispatch_indexes_var(from_inf_name)
    vtable = inf_name.get_vtable_symbol
    this_param = ident("self")
    impl_index = ident("impl_index")

  let def_impl_index = quote do:
    let `impl_index` = `dispatch_indexes`[`this_param`.impl_index][`inf_index`]

  let constructor_name = get_interface_constructor_name(inf_name)
  let inf_constructor = quote do:
    `constructor_name`(cast[RootRef](`this_param`.obj), cast[ptr `vtable`](`dispatch_table`[`impl_index`]))

  if has_interface_bases(inf_name):
    inf_constructor.add impl_index

  let
    converter_name = ident($inf_name & "Converter")
    cast_name = ident("to" & $inf_name)
    build_constructor = newStmtList(def_impl_index, inf_constructor)

  quote do:
    converter `converter_name`*(`this_param`: `from_inf_name`) : `inf_name` = `build_constructor`
    proc `cast_name`*(`this_param`: `from_inf_name`) : `inf_name` = `build_constructor`

proc add_interface_converter(inf_name: NimNode): NimNode =
  let
    bases = get_interface_bases_all(inf_name)

  result = newStmtList()
  for i, base in bases:
    if not interface_converter_created(base):
      let sub_bases = get_interface_bases_all(base)
      for j, sub_base in sub_bases:
        if j > 0:   # first item is self
          result.add add_interface_converter(base, sub_base, j)

macro impl_interface_method(inf_name: typed, exported: static[bool]) : untyped =
  result = newStmtList()

  set_interface_self(inf_name)
  if not interface_converter_created(inf_name):
    result.add create_interface_constructor(inf_name)
    result.add create_interface_method_impl(inf_name)
    result.add add_dispatch_table(inf_name)
    result.add add_interface_converter(inf_name)
    set_interface_converter_created(inf_name)

  when defined(interfacedebug):
    echo result.repr

proc remove_duplicate_record(records_list: NimNode) =
  var i = 0
  while i < records_list.len - 1:
    let namei = $(get_method_name_pair(records_list[i][0]).name)
    var j = i + 1
    while j < records_list.len:
      let namej = $(get_method_name_pair(records_list[j][0]).name)
      if namei == namej and is_same_params_type(records_list[i][1][0], records_list[j][1][0]):
        records_list.del(j)
      else:
        inc(j)
    inc(i)

proc make_ident_name_unique(ident_defs: NimNode, name: string, n: int) =
  let exported = ident_defs[0].kind == nnkPostfix
  ident_defs[0] = export_postfix(nnkAccQuoted.newTree(ident(":" & name & $n)), exported)

proc indexes_of_same_item(names: openArray[string], v: string, start: int): seq[int] =
  for i, x in names:
    if x == v: result.add i + start

proc make_name_unique(records_list: NimNode) =
  var names: seq[string]
  for ident_defs in records_list:
    names.add $(get_method_name_pair(ident_defs[0]).name)

  var fixed: seq[int]
  for i, name in names:
    if i notin fixed:
      let indexes = indexes_of_same_item(names[i..^1], name, i)
      fixed.add indexes
      if indexes.len > 1:
        for n, j in indexes:
          make_ident_name_unique(records_list[j], name, n+1)

proc create_vtable_record_list(name: NimNode, inherited: NimNode, methods: NimNode): NimNode =
  result = nnkRecList.newTree
  for base in inherited:
    for p in base.get_vtable_records_from_interface:
      result.add p

  var
    have_tostring_method = inherited.len > 0

  for meth in methods:
    meth.expectKind(nnkProcDef)
    let
      method_name = meth[0].remove_postfix

    # If the first parameter is not the interface type
    # Then we add the interface type as first parameter
    if meth.params.len < 2 or meth.params[1][1] != name:
      let this_param = newIdentDefs(ident("self"), ident($name))
      meth.params.insert(1, this_param)

    # check if there is `$` proc
    if is_tostring_method(method_name, meth.params):
      if have_tostring_method:
        continue
      else:
        have_tostring_method = true

    let vtable_entry_params = meth.params.copy
    vtable_entry_params[1][1] = ident("RootRef")

    result.add(
      nnkIdentDefs.newTree(
        method_name,
        nnkProcTy.newTree(
          vtable_entry_params,
          nnkPragma.newTree(ident("nimcall"))
        ),
        newEmptyNode(),
      )
    )
    result[^1][0] = export_postfix(method_name)

  # always add `$` if there is no `$` proc
  if not have_tostring_method:
    let tostring_proc =
      nnkProcTy.newTree(
        nnkFormalParams.newTree(
          bindSym("string"),
          newIdentDefs(
            ident("self"),
            bindSym("RootRef")
          )
        ),
        nnkPragma.newTree(ident("nimcall"))
      )

    result.add newIdentDefs(export_postfix(nnkAccQuoted.newTree(ident("$"))), tostring_proc)

  remove_duplicate_record(result)
  make_name_unique(result)

proc create_vtable_type(vtable: NimNode, vtable_record_list: NimNode): NimNode =
  nnkTypeSection.newTree(
    nnkTypeDef.newTree(
      vtable,
      newEmptyNode(),
      nnkObjectTy.newTree(
        newEmptyNode(),
        newEmptyNode(),
        vtable_record_list
      )
    )
  )

proc create_interface_type(name: NimNode, vtable_name: NimNode, id: int, with_impl_index: bool): NimNode =
  let with_impl_index = newLit(with_impl_index)
  result = quote do:
    type `name` {.InterfaceId(-1).} = object
      obj : RootRef
      vtable: ptr `vtable_name`
      when `with_impl_index`:
        impl_index: int

  result[0][0][1][0][1] = newLit(id)

macro create_interface_impl(name : untyped, methods : untyped, exported: static[bool], inherited: varargs[typed]) : untyped =
  let
    vtable_name = ident($name & "Vtable")
    vtable_record_list = create_vtable_record_list(name, inherited, methods)
    id = add_interface_info(inherited, exported)

  result = newStmtList()
  result.add create_vtable_type(export_postfix(vtable_name, exported), vtable_record_list)
  result.add create_interface_type(export_postfix(name, exported), vtable_name, id, inherited.len > 0)

  result.add newCall(bindSym"impl_interface_method", name, newLit(exported))

  when defined(interfacedebug):
    echo result.repr

macro createInterface*(name : untyped, args : varargs[untyped]) : untyped =
  name.expectKind(nnkIdent)

  result = newCall(bindSym("create_interface_impl"), name, args[^1])

  var exported = true
  var inherited: seq[NimNode]
  for i in 0 .. args.len-2:
    if args[i] == ident("false") or
      (args[i].kind == nnkExprEqExpr and args[i][0] == ident("exported") and args[i][1] == ident("false")):
        exported = false
    elif args[i].kind == nnkIdent:
      inherited.add args[i]
    else:
      error "Only ident allowed, now is " & args[i].repr

  result.add newLit(exported)
  for x in inherited:
    result.add x
