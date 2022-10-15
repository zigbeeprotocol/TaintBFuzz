module.exports = {
  root: true,
  parser: '@typescript-eslint/parser',
  plugins: [
    '@typescript-eslint',
    'import',
  ],
  extends: [
    'eslint:recommended',
    'plugin:react/recommended',
    'plugin:react-hooks/recommended',
    'plugin:@typescript-eslint/eslint-recommended',
    'plugin:@typescript-eslint/recommended',
  ],
  parserOptions: {
    project: './tsconfig.json',
  },
  settings: {
    // Electron is in devDependencies because of its special build system
    "import/core-modules": ['electron', 'react-hot-loader']
  },
  rules: {
    // --- Style rules ---

    // Force code to 80 columns, but for trailing comments
    "max-len": ["error", { "code": 80, "ignoreTrailingComments": true, }],
    // Camelcase identifers
    "camelcase": "error",
    // Do not allow functions without return type, except function expressions (arrow functions)
    "@typescript-eslint/explicit-function-return-type": [
      "error",
      {
        allowExpressions: true,
        allowTypedFunctionExpressions: true,
        allowConciseArrowFunctionExpressionsStartingWithVoid: true
      }
    ],
    // Force single class member per line
    "lines-between-class-members": [
      "error", "always", { "exceptAfterSingleLine": true }
    ],
    // Force curly brackets on newline if some item is
    "object-curly-newline": ["error", { "multiline": true }],
    // Allow infinite loops but still disallow constant if-then-else
    "no-constant-condition": ["error", { "checkLoops": false }],
    // Prefer const including when destructuring when _all_ destructured values
    // may be const
    "prefer-const": [
      "error",
      { "destructuring": "all", "ignoreReadBeforeAssign": false }
    ],
    // Disallow the use of console.* to prevent the release of code producing
    // various debuging messages
    "no-console": "error",

    // --- Safety rules ---

    // Requires semicolon at the end of each statement to prevent
    // misinterpretetion errors
    "semi": "error",
    // Be more strict on usage of useMemo and useRef
    "react-hooks/exhaustive-deps": "error",
    // Requires '+' to be applied on 2 numbers or 2 strings only
    "@typescript-eslint/restrict-plus-operands": "error",
    // Only use type safe comparison === as == between distinct type is not so obvious
    "eqeqeq": "error",
    // Disallow unused variables except variables starting with _
    "no-unused-vars": "off", // Must be turned off for the following typescript rule
    "@typescript-eslint/no-unused-vars": [
      "error", {
        "vars": "local",
        "ignoreRestSiblings": true, // Useful to remove properties using rest properties
        "varsIgnorePattern": "^_",
        "argsIgnorePattern": "^_"
      }
    ],
    // Disallow the use of var in favor of let and const
    "no-var": "error",
    // Disallow explicit any types ; common workaround includes using 'unknown'
    // when the type can't be infered
    "@typescript-eslint/no-explicit-any": "error",
  }
};
