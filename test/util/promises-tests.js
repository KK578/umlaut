const testee = require('../../util/promises.js');

describe('Promises', function () {
	describe('fs.readFile', function () {
		let method;

		before(function () {
			method = testee.fsReadFile;
		});

		it('should resolve for an existing file', function () {
			const fixture = fixtures.FullModels.SimpleMath.uml;
			const promise = testee.fsReadFile(fixture);

			return expect(promise).to.be.fulfilled;
		});

		it('should reject for a non-existing file', function () {
			const fixture = fixtures.FullModels.SimpleMath.uml + '.noexist';
			const promise = testee.fsReadFile(fixture);

			return expect(promise).to.be.rejected;
		});
	});
});
