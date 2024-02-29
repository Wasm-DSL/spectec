SPECDIR=spec
BUGDIR=spec-bugs

# Build binary

printf "[Building watsup binary ...]\n"
make

# Injecting errors

test_type() {
  local DIR=${BUGDIR}/$1
  local PATCH=${DIR}.patch
  local FILE=${DIR}/$2

  printf "\n[Injecting error to ${FILE} ...]\n"

  rm -rf ${DIR}
  cp -r ${SPECDIR} ${DIR}
  patch ${FILE} < ${PATCH}
  
  printf "\n[Running watsup on ${DIR} ...]\n"
  ./watsup ${DIR}/*.watsup
}

# Type bug 1

TYPE1DIR=type-1
TYPE1FILE=4-runtime.watsup

test_type ${TYPE1DIR} ${TYPE1FILE}

# Type bug 2

TYPE2DIR=type-2
TYPE2FILE=7-module.watsup

test_type ${TYPE2DIR} ${TYPE2FILE}

# Semantic bug 1

# Semantic bug 2

# Semantic bug 3
