# Source this file in bash or zsh.
if [ -n "${_TEAMTYPEV_OLD_PATH+x}" ]; then
    deactivate
fi
_TEAMTYPEV_OLD_PATH=$PATH
_TEAMTYPEV_OLD_DEACTIVATE=$(typeset -f deactivate 2>/dev/null || true)
deactivate() {
    PATH=$_TEAMTYPEV_OLD_PATH
    export PATH
    unset _TEAMTYPEV_OLD_PATH
    unset -f deactivate
    if [ -n "$_TEAMTYPEV_OLD_DEACTIVATE" ]; then
        eval "$_TEAMTYPEV_OLD_DEACTIVATE"
    fi
    unset _TEAMTYPEV_OLD_DEACTIVATE
    hash -r 2>/dev/null
}
PATH=@BIN@:$PATH
export PATH
hash -r 2>/dev/null
