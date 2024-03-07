SPECDIR=spec
BUGDIR=spec-bugs

# Build binary

printf "[Building watsup binary ...]\n"
make

# Injecting errors

inject() {
  printf "\nInjecting error to $3 ...\n"
  rm -rf $1
  cp -r ${SPECDIR} $1
  patch $3 < $2 &> /dev/null
}

test_type() {
  local DIR=${BUGDIR}/$1
  local PATCH=${DIR}.patch
  local FILE=${DIR}/$2

  printf "\n\n===== ${FILE} ====="
  inject ${DIR} ${PATCH} ${FILE}
 
  printf "Running watsup on ${DIR} ...\n"
  ./watsup ${DIR}/*.watsup
}

test_semantics() {
  local DIR=${BUGDIR}/$1
  local PATCH=${DIR}.patch
  local FILE=${DIR}/$2

  printf "\n\n===== ${FILE} ====="
  inject ${DIR} ${PATCH} ${FILE}
 
  printf "Running watsup on ${DIR} ...\n"
  ./watsup ${DIR}/*.watsup --animate --sideconditions --interpreter --test-interpreter test-semantics.wast > /dev/null
}

# Type bug 1

TYPE1DIR=type-1
TYPE1FILE=4-runtime.watsup

test_type ${TYPE1DIR} ${TYPE1FILE}

# Type bug 2

TYPE2DIR=type-2
TYPE2FILE=7-module.watsup

test_type ${TYPE2DIR} ${TYPE2FILE}

# Type bug 3

TYPE3DIR=type-3
TYPE3FILE=3-typing.watsup

test_type ${TYPE3DIR} ${TYPE3FILE}

# Add test file

mv test-interpreter/test-semantics.wast test-interpreter/spec-test/test-semantics.wast

# Semantics bug 1

SEM1DIR=semantics-1
SEM1FILE=6-reduction.watsup

test_semantics ${SEM1DIR} ${SEM1FILE}

# Semantics bug 2

SEM2DIR=semantics-2
SEM2FILE=6-reduction.watsup

test_semantics ${SEM2DIR} ${SEM2FILE}

# Semantics bug 3

SEM3DIR=semantics-3
SEM3FILE=6-reduction.watsup

test_semantics ${SEM3DIR} ${SEM3FILE}

# Remove test file

mv test-interpreter/spec-test/test-semantics.wast test-interpreter/test-semantics.wast 
