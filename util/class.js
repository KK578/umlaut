const SmtMethod = require('./method.js');
const path = require('path');
const fs = require('fs');

class SmtClass {
	constructor(classObject) {
		this.smtCommands = classObject.methods.map((m) => {
			const method = new SmtMethod(m);
			const commands = method.getCommands().join('\n');

			return {
				name: m.name,
				commands: commands
			};
		});
	}

	writeSMT(dir) {
		this.smtCommands.map((method) => {
			const fileName = path.join(dir, `${method.name}.smt2`);

			fs.writeFile(fileName, method.commands);
		});
	}
}

module.exports = SmtClass;
