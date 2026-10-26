# Source this file in fish.
if set -q _TEAMTYPEV_OLD_PATH
    deactivate
end
set -g _TEAMTYPEV_OLD_PATH $PATH
if functions -q deactivate
    functions -c deactivate _teamtypev_old_deactivate
end
function deactivate
    set -gx PATH $_TEAMTYPEV_OLD_PATH
    set -e _TEAMTYPEV_OLD_PATH
    functions -e deactivate
    if functions -q _teamtypev_old_deactivate
        functions -c _teamtypev_old_deactivate deactivate
        functions -e _teamtypev_old_deactivate
    end
end
set -gx PATH @BIN@ $PATH
