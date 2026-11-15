(module
                (import "wbg" "__wbindgen_memory" (func $memory (result externref)))
                (import "wbg" "__wbg_buffer_fixture" (func $buffer (param externref) (result externref)))
                (import "wbg" "ctor" (func $ctor (param externref) (result externref)))
                (import "wbg" "set" (func $set (param externref externref i32)))
                (table 16 externref)
                (memory 1)
                (global $next_slot (mut i32) (i32.const 4))
                (func $slot_alloc (result i32)
                    (local $slot i32)
                    global.get $next_slot
                    local.tee $slot
                    i32.const 1
                    i32.add
                    global.set $next_slot
                    local.get $slot)
                (func $memory_slot (result i32)
                    (local $slot i32)
                    call $slot_alloc
                    local.tee $slot
                    call $memory
                    table.set
                    local.get $slot)
                (func $buffer_slot (param $memory_slot i32) (result i32)
                    (local $value externref)
                    (local $slot i32)
                    local.get $memory_slot
                    table.get
                    call $buffer
                    local.set $value
                    call $slot_alloc
                    local.tee $slot
                    local.get $value
                    table.set
                    local.get $slot)
                (func $cleanup (param $slot i32)
                    local.get $slot
                    i32.const 2
                    i32.shl
                    i32.const 4096
                    i32.add
                    i32.const 0
                    i32.store)
                (func (export "copy") (param $source externref) (param $base i32) (result i32)
                    (local $memory_slot i32)
                    (local $buffer_slot i32)
                    (local $receiver_slot i32)
                    (local $receiver externref)
                    nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop
                    nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop
                    nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop
                    nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop nop
                    i32.const 0
                    local.get $source
                    table.set
                    call $memory_slot
                    local.tee $memory_slot
                    call $buffer_slot
                    local.tee $buffer_slot
                    table.get
                    call $ctor
                    local.set $receiver
                    call $slot_alloc
                    local.tee $receiver_slot
                    local.get $receiver
                    table.set
                    local.get $buffer_slot
                    call $cleanup
                    local.get $receiver_slot
                    table.get
                    i32.const 0
                    table.get
                    local.get $base
                    i32.const 2
                    i32.shr_u
                    call $set
                    local.get $receiver_slot
                    call $cleanup
                    local.get $memory_slot
                    call $cleanup
                    local.get $base
                    i32.load))
