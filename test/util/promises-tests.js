const testee = require('../../util/promises.js');

describe('Promises', function () {
	describe('#fs.readFile', function () {
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

	describe('#xml2js.parseString', function () {
		it('should resolve for a simple XML string', function () {
			const fixture = '<xml></xml>';
			const promise = testee.xmlParseString(fixture);

			return expect(promise).to.be.fulfilled;
		});

		it('should reject for a non XML string', function () {
			const fixture = 'FooBar';
			const promise = testee.xmlParseString(fixture);

			return expect(promise).to.be.rejected;
		});
	});
});
