const umlToSmt = require('./uml-to-smt/index.js');
const z3Runner = require('./z3-runner/index.js');

module.exports = (uml) => {
	const smt = umlToSmt(uml);

	return z3Runner(smt);
};
