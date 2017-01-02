const smtSolve = require('./smt-solver/index.js');

function generateInputs(uml) {
	return smtSolve(uml).then((smtInputs) => {
		Object.keys(smtInputs).forEach((className) => {
			const umlClass = uml[className];
			const smtClass = smtInputs[className];

			Object.keys(smtClass).forEach((methodName) => {
				const umlMethod = umlClass.methods[methodName];
				const smtMethod = smtClass[methodName];

				if (!Array.isArray(umlMethod.tests)) {
					umlMethod.tests = [];
				}

				umlMethod.tests = umlMethod.tests.concat(smtMethod);
			});
		});

		return Promise.resolve(uml);
	});
}

module.exports = (uml) => {
	return generateInputs(uml);
};
