const fs = require('fs');

function fsWriteFile(filepath, data) {
	return new Promise((resolve, reject) => {
		fs.writeFile(filepath, data, 'utf-8', (err) => {
			if (err) {
				reject(err);
			}
			else {
				resolve();
			}
		});
	});
}

module.exports = {
	fsWriteFile
};
