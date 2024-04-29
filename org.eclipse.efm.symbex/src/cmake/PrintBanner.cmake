# =============================================================================
#              CMake module: Prin project pretty banner 
# =============================================================================


include (Utils)

set(BANNER_WIDTH 100)

formatprint (${BANNER_WIDTH} "-" " " " " "")
formatprint (${BANNER_WIDTH} " " "/" "\\" "")
formatprint (${BANNER_WIDTH} " " "|" "|" "This is Diversity/Symbex Build System")
formatprint (${BANNER_WIDTH} " " "\\" "/" "")
formatprint (${BANNER_WIDTH} "-" " " " " "")

message (STATUS)
