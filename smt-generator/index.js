const SmtClass = require('./util/class.js');
const path = require('path');
const fs = require('fs');

function parseUml(uml) {
	const smtClass = new SmtClass(uml);

	return smtClass;
}

function write(smtClass, dir) {
	const classPath = path.join(dir, `smt/${smtClass.name}/`);

	smtClass.smtCommands.map((method) => {
		const filePath = path.join(classPath, `${method.name}.smt2`);

		fs.writeFile(filePath, method.commands);
	});
}

module.exports = {
	parseUml,
	write
};
