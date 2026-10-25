# Source this file in bash or zsh.
if [ -n "${_TEAMTYPE_OLD_PATH+x}" ]; then
    deactivate
fi
_TEAMTYPE_OLD_PATH=$PATH
_TEAMTYPE_OLD_DEACTIVATE=$(typeset -f deactivate 2>/dev/null || true)
deactivate() {
    PATH=$_TEAMTYPE_OLD_PATH
    export PATH
    unset _TEAMTYPE_OLD_PATH
    unset -f deactivate
    if [ -n "$_TEAMTYPE_OLD_DEACTIVATE" ]; then
        eval "$_TEAMTYPE_OLD_DEACTIVATE"
    fi
    unset _TEAMTYPE_OLD_DEACTIVATE
    hash -r 2>/dev/null
}
PATH=@BIN@:$PATH
export PATH
hash -r 2>/dev/null
