# Source this file in fish.
if set -q _TEAMTYPE_OLD_PATH
    deactivate
end
set -g _TEAMTYPE_OLD_PATH $PATH
if functions -q deactivate
    functions -c deactivate _teamtype_old_deactivate
end
function deactivate
    set -gx PATH $_TEAMTYPE_OLD_PATH
    set -e _TEAMTYPE_OLD_PATH
    functions -e deactivate
    if functions -q _teamtype_old_deactivate
        functions -c _teamtype_old_deactivate deactivate
        functions -e _teamtype_old_deactivate
    end
end
set -gx PATH @BIN@ $PATH
