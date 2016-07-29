# This file is a part of Julia. License is MIT: http://julialang.org/license

# Support for @polly

module Polly

export @polly

"""
Tells the compiler to apply the polyhedral optimizer Polly to the given function.
"""
macro polly(func)
    (isa(func, Expr) && func.head == :function) || throw(PollyError("function definition expected"))
    if Base.JLOptions().polly != 0
        esc(Base.pushmeta!(canonicalize!(func), :polly))
    end
end

# Error thrown from ill-formed uses of `@polly`
type PollyError <: Exception
    msg::String
end

# Canonicalize the given function `func`
function canonicalize!(func)
    worklist = [func]

    while !isempty(worklist)
        expr = pop!(worklist)
        for i in eachindex(expr.args)
            arg = expr.args[i]
            if isa(arg, Expr)
                if arg.head == :for
                    expr.args[i] = canonicalize_for(arg)
                    push!(worklist, arg.args[2])
                elseif arg.head == :block
                    push!(worklist, arg)
                end
            end
        end
    end

    return func
end

function canonicalize_for(loop)
    header_statements = get_header_statements(loop)
    if is_worthy(header_statements)
        next_loop_nest = loop.args[2]
        for i = length(header_statements):-1:1
            statement = header_statements[i]
            next_loop_nest = canonicalize_for(statement, next_loop_nest)
        end
        return next_loop_nest
    end
    return loop
end

function is_worthy(statements)
    for s in statements
        rhs = s.args[2]
        if length(rhs.args) == 2
            start = rhs.args[1]
            stop = rhs.args[2]
            if !isa(start, Integer) && !isa(start, Integer)
                return true
            end
        elseif length(rhs.args) == 3
            step = rhs.args[2]
            if isa(step, Integer)
                return true
            end
        end
    end
    return false
end

function get_header_statements(loop)
    loop_header = loop.args[1]
    if loop_header.head == :block
        return loop_header.args
    else
        @assert (loop_header.head == :(=) || loop_header.head == :(in)) "Unknown loop range specification"
        return [loop_header]
    end
end

function canonicalize_for(loop_header, loop_body)
    lhs = loop_header.args[1]
    rhs = loop_header.args[2]
    if rhs.head == :(:)
        induction_variable = loop_header.args[1]
        if length(rhs.args) == 2
            return canonicalize_unit_range_for(induction_variable, rhs, loop_body)
        elseif length(rhs.args) == 3
            return canonicalize_step_range_for(induction_variable, rhs, loop_body)
        end
    end
 
    quote
        for $lhs = $rhs
            $loop_body
        end
    end
end

function canonicalize_unit_range_for(induction_variable, range, loop_body)
    start = range.args[1]
    stop = range.args[2]
    return create_canonical_loop(induction_variable, start, 1, stop, loop_body) # TODO pass `one`
end

function canonicalize_step_range_for(induction_variable, range, loop_body)
    start = range.args[1]
    step = range.args[2]
    stop = range.args[3]
    if isa(step, Integer) && step != 0
        return create_canonical_loop(induction_variable, start, step, stop, loop_body)
    end

    quote
        for $induction_variable = $start:$step:$stop
            $loop_body
        end
    end
end

function create_canonical_loop(induction_variable, start, step, stop, loop_body)
    local loop_header
    local loop_footer

    i = gensym("i")

    if step > 0
        loop_header = :($i <= $stop)
    elseif step < 0
        loop_header = :($i >= $stop)
    end

    quote
        let $i = $start
            while $loop_header
                $induction_variable = $i
                let $induction_variable = $induction_variable
                    $loop_body
                end
                $i += $step
            end
        end
    end
end

end # module Polly
