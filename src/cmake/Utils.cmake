# ==============================================================================
#                 CMake module: Utilities functions
# ==============================================================================



# Formated print as a banner
function (formatprint WIDTH REPEATING_CHAR LEFTCORNER_CHAR RIGHTCORNER_CHAR TEXT)
    if (TEXT)
        string (LENGTH ${TEXT} TEXT_LENGTH)
        math (EXPR TEXT_LENGTH_MODULO2  "${TEXT_LENGTH} % 2")
        if (TEXT_LENGTH_MODULO2)
            set (TEXT "${TEXT} ")
            string (LENGTH ${TEXT} TEXT_LENGTH)
        endif()
    else ()
        set (TEXT_LENGTH 0)
    endif() 
    math (EXPR HALFLINE_LENGTH "(${WIDTH} - ${TEXT_LENGTH}) / 2 - 2")
    set (RESULT ${TEXT})
    foreach (DUMMY RANGE ${HALFLINE_LENGTH})
        set (RESULT "${REPEATING_CHAR}${RESULT}${REPEATING_CHAR}")
    endforeach()
    set (RESULT "${LEFTCORNER_CHAR}${RESULT}${RIGHTCORNER_CHAR}")
    message (STATUS ${RESULT})
    unset (TEXT_LENGTH)
endfunction (formatprint)


# Print each element of a list on its own line
function (listprint TEXT)
  if (TEXT)
    foreach (LINE ${TEXT})
      message (STATUS ${LINE})
    endforeach()
  endif()
endfunction (listprint)



