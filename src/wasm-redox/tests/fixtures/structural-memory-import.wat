(module
                (import "wbg" "__wbindgen_memory" (func $memory (result externref)))
                (import "wbg" "ctor" (func $ctor (param externref) (result externref)))
                (import "wbg" "set" (func $set (param externref externref i32)))
                (table 4 externref)
                (memory (export "memory") 1)
                (func $memory_slot (result i32)
                    (local $slot i32)
                    i32.const 2
                    local.tee $slot
                    call $memory
                    table.set
                    local.get $slot)
                (func $buffer_slot (param $slot i32) (result i32)
                    local.get $slot)
                (func (export "copy") (param $source externref) (param $base i32) (result i32)
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    nop
                    i32.const 0
                    local.get $source
                    table.set

                    i32.const 1
                    call $memory_slot
                    call $buffer_slot
                    table.get
                    call $ctor
                    table.set

                    i32.const 1
                    table.get
                    i32.const 0
                    table.get
                    local.get $base
                    i32.const 2
                    i32.shr_u
                    call $set

                    local.get $base
                    i32.load
                    local.get $base
                    i32.load offset=4
                    i32.add))
