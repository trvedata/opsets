function capitalise(str) {
    return toupper(substr(str, 1, 1)) substr(str, 2)
}

function uncapitalise(str) {
    return tolower(substr(str, 1, 1)) substr(str, 2)
}

function camelCase(str,       i, pieces, result) {
    patsplit(str, pieces, /[^_]+/)
    for (i in pieces) {
        if (i == 1) {
            result = uncapitalise(pieces[1])
        } else {
            result = result capitalise(pieces[i])
        }
    }
    return result
}

function formatAtom(str,       i, matches, tokens, final, result) {
    if (match(str, /^(\w+) < (\w+)$/, matches)) {
        return "\\mathit{" capitalise(matches[1]) "} < \\mathit{" capitalise(matches[2]) "}"
    }

    if (match(str, /^\\<D> +(\w+) *= *Some *\(?([^\)]+)\)?$/, matches)) {
        return "\\mathit{" capitalise(matches[1]) "} \\mapsto " formatAtom(matches[2])
    }

    result = ""
    if (sub(/^\\<not> */, "", str)) result = "\\neg\\;"

    if (str ~ /\\/) {
        print "Unparsed backslash in atom:", str > "/dev/stderr"
        next
    }

    patsplit(str, tokens, /[^ ]+/)
    for (i in tokens) {
        if (i == 1) {
            result = result "\\mathrm{" camelCase(tokens[1]) "}"
            final = ""
        } else {
            if (i > 2) {
                result = result ", "
            } else {
                result = result "("
                final = ")"
            }
            result = result "\\mathit{" capitalise(tokens[i]) "}"
        }
    }
    return result final
}

/lbrakk/ {
    if (match($0, /"\\<lbrakk>(.*)\\<rbrakk> *\\<Longrightarrow> *(.*)"/, rule) == 0) {
        print "Could not match line:", $0 > "/dev/stderr"
        next
    } 

    latex = formatAtom(rule[2]) " \\leftarrow\\; &\n"

    patsplit(rule[1], body, /[^ ;]+[^;]*/)
    for (i in body) {
        if (i > 1) latex = latex ",\n"
        latex = latex "    " formatAtom(body[i])
    }

    print latex ".\\\\"
}
